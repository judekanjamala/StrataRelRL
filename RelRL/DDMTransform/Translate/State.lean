/-
  Copyright StrataRelRL Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module

public import RelRL.DDMTransform.Translate.Priming

namespace Strata
namespace RelRL

public section

open StrataDDM (Operation Arg QualifiedIdent)

/-! # What a biproc body accumulates, and the checks over it

`Side` and `Mode` say which program is being talked about and which reading of
the bicommand is being produced; `BodyState` carries the rest. The checks here
are what report a duplicate declaration or a one-sided name against the source,
rather than leaving it to Core against the translated program. -/

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

/-- The Core name a source name takes on `side`. Self-composition fuses both
programs into one Core scope, so this is the name that must be unique. -/
def Side.core_name : Side → String → String
  | .left, x => x
  | .right, x => x ++ "'"

/-- A name already standing in the fused block: what it collides *as*, plus
enough of where it came from for the message to say so. -/
structure DeclName where
  core : String
  source : String
  side : Side

/-- `verify` fuses the two sides by self-composition; `project` keeps one of them
as a unary program, unprimed and stripped of relational formulas
(`docs/workflows/project.md`). -/
inductive Mode where
  | verify
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
       {prev.side.name} program: self-composition names both `{core}`"

/-- Record `names` as declared on `side`, reporting any the fused block already
holds. Only `.verify` fuses; a projection is one unary program, which Core
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

/-- Report any name `stmts` mentions that `side` has nothing declared for. The
fragment's own declarations count. `declared` also holds split locals from
earlier bicommands, which are block-scoped by then — so this under-reports
rather than over-reports, which is the safe direction for a check whose job is
to replace a Core error with a better one. -/
def BodyState.check_side (s : BodyState) (fr : FileRange) (side : Side)
    (stmts : List Core.Statement) : BodyState :=
  let own := (Imperative.HasVarsImp.definedVars (P := Core.Expression) stmts false).map (·.name)
  let declared := s.declared.filterMap fun d => if d.side == side then some d.source else none
  (fragment_names stmts).foldl (init := s) fun s name =>
    if own.contains name || declared.contains name then s
    else
      { s with diagnostics := s.diagnostics.push <|
          Message.withRange fr s!"the {side.name} program has no `{name}`" .userError }

/-- The same for a lowered formula, which names both programs at once and so is
checked against Core names — a left declaration under its source name, a right
one under its prime. This is also what catches `Agree x` for an `x` neither
program declares, since that form is built lexically. -/
def check_formula (declared : List DeclName) (fr : FileRange)
    (e : Core.Expression.Expr) : Array Message :=
  (expr_names e).foldl (init := #[]) fun ds name =>
    if declared.any (·.core == name) then ds
    else
      -- Which program it would have belonged to, for the message. A left name
      -- spelled with a prime is rejected earlier, by the collision check.
      let (side, source) :=
        if name.endsWith "'" then ("right", name.dropEnd 1) else ("left", name)
      ds.push <| Message.withRange fr
        s!"`{source}` is not a variable of the {side} program" .userError

/-- Emit one bicommand: the left program's statements, then the right's, as
WhyRel's `Bisplit` does. Per bicommand, never per side — CLAUDE.md, "Emission
order is per bicommand". -/
def BodyState.emit (s : BodyState) (left right : List Core.Statement) : BodyState :=
  { s with out := s.out ++ left.toArray ++ right.toArray }

end
end RelRL
end Strata
