/-
  Copyright StrataRelRL Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module

public import RelRL.DDMTransform.Translate.Priming
public import Strata.Languages.Core.Verifier
public import Strata.Pipeline.Messages
import StrataDDM.AST

namespace Strata
namespace RelRL

public section

open StrataDDM (Arg)

/-! # What a biproc body accumulates, and the checks over it

`Side` and `Mode` say which program is being talked about and what translation
of the bicommand is being produced; `BodyState` carries the rest. The checks
here are what report a duplicate declaration or a one-sided name against the
source, rather than leaving it to Core against the translated program. -/

/-- Which program a projection keeps. -/
inductive Side where
  | left
  | right
  deriving DecidableEq, Repr

def Side.of_string? : String → Option Side
  | "left" => some .left
  | "right" => some .right
  | _ => none

def Side.name : Side → String
  | .left => "left"
  | .right => "right"

/-- The Core name a source name takes on `side`. Composing the two programs
puts them in one Core scope, so this is the name that must be unique. -/
def Side.core_name : Side → String → String
  | .left, x => x
  | .right, x => x ++ "'"

/-- A name already standing in the fused block: what it collides *as*, plus
enough of where it came from for the message to say so. -/
structure DeclName where
  core : String
  source : String
  side : Side

/--
`.compose` puts both programs in one procedure, the right one primed. `.project`
keeps one side's statements from every bicommand in order and nothing of the
other's. It drops every relational formula — spec, `Assert`, etc.
 -/
inductive Mode where
  | compose
  | project (side : Side)
  deriving Repr

/-- What a `biproc` body accumulates. One output stream: each bicommand emits
its left program's statements and then its right program's, immediately. -/
structure BodyState where
  bindings : TransBindings
  out : Array Core.Statement := #[]
  asserts : Nat := 0
  assumes : Nat := 0
  /-- Everything declared into the fused block so far, newest first. -/
  declared : List DeclName := []
  /-- Errors in the source program, located. Distinct from `TransM.error`,
  which reports a broken translator invariant and exits 3. -/
  diagnostics : Array Message := #[]

/-- `TransM.error` needs a fallback value; `TransBindings` has all-default
fields, so an empty accumulator is the natural one. The `TransBindings` instance
is for the same reason — Core does not declare one, and `lower_params` returns a
tuple containing it. -/
instance : Inhabited TransBindings := ⟨{}⟩
instance : Inhabited BodyState := ⟨{ bindings := {} }⟩

def collision_message (name : String) (side : Side) (core : String) (prev : DeclName) : String :=
  if prev.source == name && prev.side == side then
    s!"`{name}` is declared twice in the {side.name} program"
  else
    s!"`{name}` in the {side.name} program collides with `{prev.source}` in the \
       {prev.side.name} program: composing the two names both `{core}`"

/-- Record `names` as declared on `side`, reporting any the fused block already
holds. Only `.compose` fuses; a projection is one unary program, which Core
checks on its own. -/
def BodyState.declare (s : BodyState) (fr : FileRange) (side : Side)
    (names : List String) : BodyState :=
  names.foldl (init := s) fun s name =>
    let core := side.core_name name
    match s.declared.find? (·.core == core) with
    | some prev =>
      { s with diagnostics := s.diagnostics.push <|
          Message.withRange fr (collision_message name side core prev) .userError }
    | none => { s with declared := ⟨core, name, side⟩ :: s.declared }

/-- `old x` lowers to an fvar named `"old x"` (`Core.CoreIdent.mkOld`), so a
check against declared names has to look past the prefix. Priming needs no such
help: `"old x" ++ "'"` is `"old x'"`, which is the right program's old `x`. -/
def strip_old (name : String) : String :=
  if name.startsWith Core.CoreIdent.oldStr then
    (name.drop Core.CoreIdent.oldStr.length).toString
  else name

/-- Report any name `stmts` mentions that `side` has nothing declared for. Every
entry in `declared` is in scope by construction — only `Var` and the parameters
put one there — so the check is against all of them. The fragment's own
declarations count too, which is what lets a Core `var` nested in an `if` or
`while` body be read below itself. -/
def BodyState.check_side (s : BodyState) (fr : FileRange) (side : Side)
    (stmts : List Core.Statement) : BodyState :=
  let own := (Imperative.HasVarsImp.definedVars (P := Core.Expression) stmts false).map (·.name)
  let declared := s.declared.filterMap fun d =>
    if d.side == side then some d.source else none
  (fragment_names stmts).foldl (init := s) fun s n =>
    let name := strip_old n
    if own.contains name || declared.contains name then s
    else
      { s with diagnostics := s.diagnostics.push <|
          Message.withRange fr s!"the {side.name} program has no `{name}`" .userError }

/-- The same for a lowered formula, which names both programs at once and so is
checked against Core names — a left declaration under its source name, a right
one under its prime. This is what catches a formula naming an `x` only one
program declares: DDM resolved it against the scope chain, which holds both. -/
def check_formula (declared : List DeclName) (fr : FileRange)
    (e : Core.Expression.Expr) : Array Message :=
  (expr_names e).foldl (init := #[]) fun ds n =>
    let name := strip_old n
    if declared.any (fun d => d.core == name) then ds
    else
      -- Which program it would have belonged to, for the message. A left name
      -- spelled with a prime is rejected earlier, by the collision check.
      let (side, source) :=
        if name.endsWith "'" then ("right", name.dropEnd 1) else ("left", name)
      ds.push <| Message.withRange fr
        s!"`{source}` is not a variable of the {side} program" .userError

/-- The names a `DeclList` binds, in source order. -/
partial def decl_list_names (a : Arg) : List String :=
  match a with
  | .op op =>
    match op.name, op.args with
    | q`Core.declAtom, #[b] => decl_list_names b
    | q`Core.declPush, #[dl, b] => decl_list_names dl ++ decl_list_names b
    | q`Core.bind_mk, #[.ident _ v, _, _] => [v]
    | _, _ => []
  | _ => []

/-- Refuse a relational quantifier binding one name on both sides. DDM resolves
every occurrence to the inner binder, so the outer one is unreachable and the
formula quietly says less than it reads as — `Forall i | i :: i =:= i` lowers to
`forall i, i :: i == i`, which is a tautology. Walked over the whole `biproc`,
so a quantifier in a spec, an invariant, an `Assert` or an alignment guard is
reached the same way. -/
partial def check_quant_binders (file : String) (a : Arg) : Array Message :=
  let below (args : Array Arg) : Array Message :=
    args.foldl (fun ds x => ds ++ check_quant_binders file x) #[]
  match a with
  | .op op =>
    match op.name, op.args with
    | q`RelRL.biq_both, #[l, r] =>
      let ls := decl_list_names l
      ((decl_list_names r).filter (ls.contains ·)).foldl (init := below op.args) fun ds n =>
        ds.push <| Message.withRange { file := .file file, range := op.ann }
          s!"a relational quantifier binds `{n}` on both sides: every use resolves \
             to the right one, so the left binder is unreachable. Give them \
             different names, or bind one list both sides share." .userError
    | _, _ => below op.args
  | .seq _ _ as => below as
  | .option _ (some b) => check_quant_binders file b
  | _ => #[]

/-- Emit one bicommand: the left program's statements, then the right's, as
WhyRel's `Bisplit` does. Per bicommand, never per side — CLAUDE.md, "Emission
order is per bicommand". -/
def BodyState.emit (s : BodyState) (left right : List Core.Statement) : BodyState :=
  { s with out := s.out ++ left.toArray ++ right.toArray }

end
end RelRL
end Strata
