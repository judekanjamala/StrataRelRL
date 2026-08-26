/-
  Copyright StrataRelRL Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module

public import RelRL.DDMTransform.Grammar
public import Strata.Languages.Core.Verifier
public import Strata.DL.Imperative.MetaData
public import Strata.Pipeline.Messages
import StrataDDM.AST

namespace Strata
namespace RelRL

public section

open StrataDDM (Operation Arg QualifiedIdent)

/-! # RelRL to Core translation

`biproc name = << left | right >> ensures …;` becomes a Core procedure `name`.
Left-side top-level locals keep their names, right-side ones are primed
(`<v>'`), and the sides are concatenated — self-composition — so an `ensures`
agreement is an ordinary Core `assert` after both have run. Per-declaration
translation is delegated to Core's own `Core.getProgram` rather than
reimplemented. See `docs/workflow.md`. -/

structure TranslateState where
  diagnostics : Array Message := #[]

abbrev TranslateM := StateM TranslateState

def TranslateM.run (m : TranslateM α) : α × Array Message :=
  let (v, s) := StateT.run m {}
  (v, s.diagnostics)

def emit_diagnostic (d : Message) : TranslateM Unit :=
  modify fun s => { s with diagnostics := s.diagnostics.push d }

/-- Report a broken translator invariant. `Grammar.lean` fixes every argument
shape matched below, so the fallback branches are unreachable through the
parser; if one fires the grammar and translator have drifted, which is a bug
here rather than in the user's program. `.strataBug` makes it exit 3. -/
def emit_invariant_violation (msg : String) : TranslateM Unit :=
  emit_diagnostic (Message.fromString s!"translator invariant violated: {msg}" .strataBug)

/-- Translate one ordinary Core top-level operation by wrapping it in a
singleton Core program and delegating to `Core.getProgram`. -/
def translate_core_op (op : Operation) (ictx : Lean.Parser.InputContext) :
    TranslateM (List Core.Decl) := do
  let singleton := StrataDDM.Program.create Core_map "Core" #[op]
  let (coreProgram, errors) := Core.getProgram singleton ictx
  for e in errors do
    emit_diagnostic (Message.fromString e .strataBug)
  return coreProgram.decls

/-- Undo the `Core.command_block` wrap from `lower_block_arg`: Core turns such a
command into a nameless procedure, so peel it back to a statement list. -/
def unwrap_block_procedure (label : String) (decls : List Core.Decl) :
    TranslateM (List Core.Statement) := do
  match decls with
  | [.proc proc _md] =>
    match proc.body with
    | .structured ss => return ss
    | .cfg _ =>
      emit_invariant_violation s!"biembed {label} side lowered to a CFG block"
      return []
  | _ =>
    emit_invariant_violation
      s!"biembed {label} side lowered to {decls.length} decls, expected one procedure"
    return []

/-- Prime a side's top-level declarations so the two sides can be flattened
without colliding, and so an `ensures` spec can name them. The left side is
translated with `sfx = ""` (unprimed, so it keeps the source names) and the
right with `sfx = "'"`. `substFvar` rewrites reads, `renameLhs` rewrites
targets. Declarations nested in an `if`/`while` body stay block-scoped, so they
neither collide nor can be named. -/
def suffix_side_vars (sfx : String) (stmts : List Core.Statement) : List Core.Statement :=
  if sfx.isEmpty then stmts else
  let declared := stmts.filterMap fun
    | .init lhs _ _ _ => some lhs.name
    | _ => none
  declared.foldl (init := stmts) fun ss v =>
    let v' : Core.CoreIdent := ⟨v ++ sfx, ()⟩
    Core.Block.renameLhs (Core.Block.substFvar ss ⟨v, ()⟩ (.fvar () v' none)) ⟨v, ()⟩ v'

/-- Lower one side to renamed statements: `label` names the side in diagnostics,
`sfx` is the suffix its top-level locals take. The argument is a Core `Block`,
so it is wrapped in a synthetic `Core.command_block` to become a top-level
`Command` that `Core.getProgram` accepts. -/
def lower_block_arg (label sfx : String) (arg : Arg) (ictx : Lean.Parser.InputContext) :
    TranslateM (List Core.Statement) := do
  match arg with
  | .op blockOp =>
    let asCommand : Operation :=
      { ann := blockOp.ann, name := q`Core.command_block, args := #[.op blockOp] }
    let decls ← translate_core_op asCommand ictx
    let stmts ← unwrap_block_procedure label decls
    return suffix_side_vars sfx stmts
  | _ =>
    emit_invariant_violation s!"biembed {label} side is not an operation"
    return []

/-- Lower `biembed left right` to one flat statement list. Flattened rather than
nested because a Core block's locals are invisible once it closes, and an
`ensures` spec must name both sides. Not recursive: `Bicommand` cannot occur
inside a side. -/
def lower_bicommand (op : Operation) (ictx : Lean.Parser.InputContext) :
    TranslateM (List Core.Statement) := do
  match op.args with
  | #[left, right] =>
    return (← lower_block_arg "left" "" left ictx) ++ (← lower_block_arg "right" "'" right ictx)
  | _ =>
    emit_invariant_violation "biembed does not have exactly two arguments"
    return []

/-- Lower one `rel_agree` — `[l]: x == y` — to a Core `assert`. Both operands are
identifiers by construction, so the equality is built directly. -/
def lower_rel_agree (arg : Arg) (ictx : Lean.Parser.InputContext) :
    TranslateM (List Core.Statement) := do
  match arg with
  | .op specOp =>
    match specOp.args with
    | #[.ident _ label, .ident _ lhs, .ident _ rhs] =>
      let md := Imperative.MetaData.ofSourceRange (.file ictx.fileName) specOp.ann
      let l : Core.Expression.Expr := .fvar () ⟨lhs, ()⟩ none
      let r : Core.Expression.Expr := .fvar () ⟨rhs, ()⟩ none
      return [.assert label (.eq () l r) md]
    | _ =>
      emit_invariant_violation "rel_agree does not have exactly three identifiers"
      return []
  | _ =>
    emit_invariant_violation "rel_agree spec is not an operation"
    return []

/-- Lower the optional `ensures` clause to asserts appended after both sides. -/
def lower_rel_ensures (arg : Arg) (ictx : Lean.Parser.InputContext) :
    TranslateM (List Core.Statement) := do
  match arg with
  | .option _ none => return []
  | .option _ (some (.op ensuresOp)) =>
    match ensuresOp.args with
    | #[.seq _ _ specs] =>
      -- Reversed accumulator, flipped once: `stmts ++ …` per iteration is O(n²).
      let mut acc : List (List Core.Statement) := []
      for spec in specs do
        acc := (← lower_rel_agree spec ictx) :: acc
      return acc.reverse.flatten
    | _ =>
      emit_invariant_violation "rel_ensures does not hold a comma-separated sequence"
      return []
  | _ =>
    emit_invariant_violation "biproc's rel argument is not an Option"
    return []

/-- Each `RelRL.biproc` becomes a Core procedure of the same name; every other
top-level command is ordinary Core syntax, delegated unchanged. -/
def translate_program (p : StrataDDM.Program)
    (ictx : Lean.Parser.InputContext := Inhabited.default) : TranslateM Core.Program := do
  let mut acc : List (List Core.Decl) := []
  for op in p.commands do
    if op.name == q`RelRL.biproc then
      match op.args with
      | #[.ident _ name, .op bicommandOp, relArg] =>
        let sideStmts ← lower_bicommand bicommandOp ictx
        let relStmts ← lower_rel_ensures relArg ictx
        let md := Imperative.MetaData.ofSourceRange (.file ictx.fileName) op.ann
        let body : Core.Statement := .block "biembed" (sideStmts ++ relStmts) md
        acc := [.proc
          { header := { name := name, typeArgs := [], inputs := [], outputs := [] },
            spec := { preconditions := [], postconditions := [] },
            body := .structured [body] } md] :: acc
      | _ =>
        emit_invariant_violation "biproc does not have exactly three arguments"
    else
      acc := (← translate_core_op op ictx) :: acc
  return { decls := acc.reverse.flatten }

end
end RelRL
end Strata
