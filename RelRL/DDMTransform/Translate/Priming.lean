/-
  Copyright StrataRelRL Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module

public import Strata.Languages.Core.Verifier

namespace Strata
namespace RelRL

public section

/-! ## Priming

A right-hand fragment is renamed apart before the two sides are emitted
together.
Both helpers fold Core's own substitution, so no traversal is written here.

**What gets primed is every program variable the fragment mentions.** Core has
no top-level variables — a constant is a 0-ary function, so it lowers to `.op`
and never to `.fvar` — which is what makes that safe: the only names these
helpers can reach are the two programs' own locals, and on the right side every
one of them belongs to the right program. Renaming against a list of *expected*
names instead would let anything off that list fall through to the left
program's variable; CLAUDE.md, "The other invariant", says not to. -/

/-- Top-level declared names. One nested in an `if`/`while` body stays
block-scoped, so it cannot collide across sides. Used for the collision check,
not for priming. -/
def top_level_declared (stmts : List Core.Statement) : List String :=
  stmts.filterMap fun
    | .init lhs _ _ _ => some lhs.name
    | _ => none

/-- Every program variable a statement fragment mentions — declared, assigned
or read, at any depth. -/
def fragment_names (stmts : List Core.Statement) : List String :=
  let ids := Imperative.HasVarsImp.definedVars (P := Core.Expression) stmts false
    ++ Imperative.HasVarsImp.modifiedVars (P := Core.Expression) stmts
    ++ Imperative.HasVarsImp.readVars (P := Core.Expression) stmts
  (ids.map (·.name)).eraseDups

/-- The same, for an expression. -/
def expr_names (e : Core.Expression.Expr) : List String :=
  ((Imperative.HasFvars.getFvars (P := Core.Expression) e).map (·.name)).eraseDups

/-- Renaming is a *sequential* fold over Core's own substitution, so a name
whose primed form is also in the list would be primed twice — `{n, n'}` sends
`n` to `n''` if `n` goes first. Longest first makes that impossible: `x'` is
always longer than `x`, so it is already renamed when `x` produces one. -/
def longest_first (names : List String) : List String :=
  names.mergeSort (fun a b => b.length ≤ a.length)

def prime_stmts (names : List String) (stmts : List Core.Statement) : List Core.Statement :=
  (longest_first names).foldl (init := stmts) fun ss v =>
    let v' : Core.CoreIdent := ⟨v ++ "'", ()⟩
    Core.Block.renameLhs (Core.Block.substFvar ss ⟨v, ()⟩ (.fvar () v' none)) ⟨v, ()⟩ v'

def prime_expr (names : List String) (e : Core.Expression.Expr) : Core.Expression.Expr :=
  (longest_first names).foldl (init := e) fun acc v =>
    Lambda.LExpr.substFvar acc ⟨v, ()⟩ (.fvar () ⟨v ++ "'", ()⟩ none)

end
end RelRL
end Strata
