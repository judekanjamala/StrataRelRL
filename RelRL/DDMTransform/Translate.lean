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

`birelate name = (left | right);` lowers to a Core procedure named `name` whose
body is a single statement block containing two labeled sub-blocks, `left`
followed by `right`, executed as one sequential Core program: left and right
remain separate namespaces (Core scoping, not aliasing), so no shared heap or
state is introduced between the two sides.

Core's own DDM translator (`Core.getProgram`), reusing exactly the same
battle-tested per-statement/per-declaration translation Core itself uses instead
of re-implementing it. -/

structure TranslateState where
  diagnostics : Array Message := #[]

abbrev TranslateM := StateM TranslateState

def TranslateM.run (m : TranslateM α) : α × Array Message :=
  let (v, s) := StateT.run m {}
  (v, s.diagnostics)

def emitDiagnostic (d : Message) : TranslateM Unit :=
  modify fun s => { s with diagnostics := s.diagnostics.push d }

/-- Translate an ordinary Core-syntax top-level operation (a function,
procedure, type declaration, or bare block) by delegating to Core's own DDM
translator. The operation is wrapped in a singleton Core program so that
`Core.getProgram` can be reused unchanged. -/
def translateCoreOp (op : Operation) (ictx : Lean.Parser.InputContext) :
    TranslateM (List Core.Decl) := do
  let singleton := StrataDDM.Program.create Core_map "Core" #[op]
  let (coreProgram, errors) := Core.getProgram singleton ictx
  for e in errors do
    emitDiagnostic (Message.fromString e .strataBug)
  return coreProgram.decls

/-- Undo the `Core.command_block` wrap applied in `lowerBlockArg`. Core
translates such a command to a single nameless, parameterless procedure whose
body is the block's statements, so peel that procedure off and return the
statements for embedding in the combined `biembed` block. `label` (`left` or
`right`) is used only in diagnostics. -/
def unwrapBlockProcedure (label : String) (decls : List Core.Decl) :
    TranslateM (List Core.Statement) := do
  match decls with
  | [.proc proc _md] =>
    match proc.body with
    | .structured ss => return ss
    | .cfg _ =>
      emitDiagnostic (Message.fromString
        s!"biembed {label} side must be structured Core syntax, not a CFG block")
      return []
  | _ =>
    emitDiagnostic (Message.fromString
      s!"biembed {label} side must be a single Core statement block")
    return []

/-- Prefix every variable a side declares, so the two sides can be flattened
into one scope without colliding — and so a relational spec can name them.
`substFvar` rewrites reads, `renameLhs` rewrites declaration and assignment
targets; together they are a full rename.

Only the side's *top-level* declarations are renamed. A declaration nested in
an `if` or `while` body stays block-scoped, so it can neither collide across
sides nor be named by a spec. -/
def prefixSideVars (pfx : String) (stmts : List Core.Statement) : List Core.Statement :=
  let declared := stmts.filterMap fun
    | .init lhs _ _ _ => some lhs.name
    | _ => none
  declared.foldl (init := stmts) fun ss v =>
    let v' : Core.CoreIdent := ⟨pfx ++ v, ()⟩
    Core.Block.renameLhs (Core.Block.substFvar ss ⟨v, ()⟩ (.fvar () v' none)) ⟨v, ()⟩ v'

/-- Lower one side of a `biembed` to its statements, with every top-level
declaration prefixed by `label ++ "_"`. The argument is a Core `Block`
operation; wrapping it in `Core.command_block` turns it into the top-level
`Command` that `Core.getProgram` knows how to translate, so Core's own block
handling is reused verbatim. -/
def lowerBlockArg (label : String) (arg : Arg) (ictx : Lean.Parser.InputContext) :
    TranslateM (List Core.Statement) := do
  match arg with
  | .op blockOp =>
    let asCommand : Operation :=
      { ann := blockOp.ann, name := q`Core.command_block, args := #[.op blockOp] }
    let decls ← translateCoreOp asCommand ictx
    let stmts ← unwrapBlockProcedure label decls
    return prefixSideVars s!"{label}_" stmts
  | _ =>
    emitDiagnostic (Message.fromString s!"biembed {label} side must be a block")
    return []

/-- Lower a `biembed` operation's two `Block`-typed arguments (`left`, `right`)
to one flat statement list: the left side's statements followed by the right
side's, each side's locals renamed `left_<v>` / `right_<v>`.

The sides are flattened rather than nested in `left:` / `right:` blocks so that
a relational spec can refer to both sides at once — block-scoped variables are
invisible once the block closes. Renaming keeps them disjoint, which makes this
ordinary self-composition, sound for the forall-forall fragment.

Not recursive: a `Bicommand` cannot occur inside either side (see the module
docstring). -/
def lowerBicommand (op : Operation) (ictx : Lean.Parser.InputContext) :
    TranslateM (List Core.Statement) := do
  match op.args with
  | #[left, right] =>
    let leftStmts ← lowerBlockArg "left" left ictx
    let rightStmts ← lowerBlockArg "right" right ictx
    return leftStmts ++ rightStmts
  | _ =>
    emitDiagnostic (Message.fromString "biembed expects exactly two blocks (left, right)")
    return []

/-- Lower one `RelRL.rel_agree` — `[l]: x == y` — to a Core `assert`. Both
operands are identifiers by construction (see `Grammar.lean`), so the equality
is built directly rather than routed through Core's expression translator. -/
def lowerRelAgree (arg : Arg) (ictx : Lean.Parser.InputContext) :
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
      emitDiagnostic (Message.fromString "malformed relational spec")
      return []
  | _ =>
    emitDiagnostic (Message.fromString "malformed relational spec")
    return []

/-- Lower a `birelate`'s optional `ensures` clause to a list of Core asserts,
appended after both sides have run. An absent clause yields no statements. -/
def lowerRelEnsures (arg : Arg) (ictx : Lean.Parser.InputContext) :
    TranslateM (List Core.Statement) := do
  match arg with
  | .option _ none => return []
  | .option _ (some (.op ensuresOp)) =>
    match ensuresOp.args with
    | #[.seq _ _ specs] =>
      let mut stmts : List Core.Statement := []
      for spec in specs do
        stmts := stmts ++ (← lowerRelAgree spec ictx)
      return stmts
    | _ =>
      emitDiagnostic (Message.fromString "malformed ensures clause")
      return []
  | _ =>
    emitDiagnostic (Message.fromString "malformed ensures clause")
    return []

/-- Translate a whole RelRL program to Core: each top-level `RelRL.birelate`
becomes a Core procedure of the same name whose body is the lowered `biembed`
block; every other top-level command is ordinary Core syntax, translated
unchanged via `Core.getProgram`. -/
def translateProgram (p : StrataDDM.Program)
    (ictx : Lean.Parser.InputContext := Inhabited.default) : TranslateM Core.Program := do
  let mut decls : List Core.Decl := []
  for op in p.commands do
    if op.name == q`RelRL.birelate then
      match op.args with
      | #[.ident _ name, .op bicommandOp, relArg] =>
        let sideStmts ← lowerBicommand bicommandOp ictx
        let relStmts ← lowerRelEnsures relArg ictx
        let md := Imperative.MetaData.ofSourceRange (.file ictx.fileName) op.ann
        let body : Core.Statement := .block "biembed" (sideStmts ++ relStmts) md
        decls := decls ++ [.proc
          { header := { name := name, typeArgs := [], inputs := [], outputs := [] },
            spec := { preconditions := [], postconditions := [] },
            body := .structured [body] } md]
      | _ =>
        emitDiagnostic (Message.fromString "malformed birelate declaration")
    else
      let subDecls ← translateCoreOp op ictx
      decls := decls ++ subDecls
  return { decls := decls }

end
end RelRL
end Strata
