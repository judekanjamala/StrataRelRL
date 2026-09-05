/-
  Copyright StrataRelRL Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module

public import RelRL.DDMTransform.Translate.Priming
public import Strata.Languages.Core.Verifier
import StrataDDM.AST

namespace Strata
namespace RelRL

public section

open StrataDDM (Arg)

/-! # Relational formulas

A formula becomes one Core `bool` expression. `Grammar.lean` lists what each
form means. `Agree` and `Both` are absent: `Desugar.lean` rewrote both away
before this ran. -/

/-- Apply one of Core's boolean operators. A relational formula has no Core
surface syntax to route through `translateFnTable`, so it builds the same
applications directly. -/
def bool_app (op : Core.Expression.Expr) (args : List Core.Expression.Expr) :
    Core.Expression.Expr :=
  Lambda.LExpr.mkApp () op args

/-- Lower a relational formula to one Core `bool` expression. `Grammar.lean`
lists what each form means; here, "the right state" is just the primed reading —
a right-hand fragment has every variable it mentions renamed. -/
partial def lower_rformula (p : StrataDDM.Program) (bindings : TransBindings)
    (arg : Arg) : TransM Core.Expression.Expr := do
  match arg with
  | .op op =>
    match op.name, op.args with
    | q`RelRL.rf_left, #[e] =>
      translateExpr p bindings e
    | q`RelRL.rf_right, #[e] =>
      let e ← translateExpr p bindings e
      return prime_expr (expr_names e) e
    | q`RelRL.rf_biequal, #[_, l, r] =>
      let l ← translateExpr p bindings l
      let r ← translateExpr p bindings r
      return .eq () l (prime_expr (expr_names r) r)
    | q`RelRL.rf_group, #[r] =>
      lower_rformula p bindings r
    | q`RelRL.rf_not, #[r] =>
      return bool_app Core.boolNotOp [← lower_rformula p bindings r]
    | q`RelRL.rf_and, #[l, r] =>
      return bool_app Core.boolAndOp
        [← lower_rformula p bindings l, ← lower_rformula p bindings r]
    | q`RelRL.rf_or, #[l, r] =>
      return bool_app Core.boolOrOp
        [← lower_rformula p bindings l, ← lower_rformula p bindings r]
    | q`RelRL.rf_implies, #[l, r] =>
      return bool_app Core.boolImpliesOp
        [← lower_rformula p bindings l, ← lower_rformula p bindings r]
    | q`RelRL.rf_iff, #[l, r] =>
      return bool_app Core.boolEquivOp
        [← lower_rformula p bindings l, ← lower_rformula p bindings r]
    | n, args =>
      TransM.error s!"unexpected relational formula {n.fullName} with {args.size} arguments"
  | _ => TransM.error "relational formula is not an operation"

/-- Peel a formula's top-level `/\` so each conjunct becomes its own proof
obligation. `{ … }` is transparent to this; every other connective is opaque,
since its parts are not separately provable. -/
partial def top_conjuncts (arg : Arg) : List Arg :=
  match arg with
  | .op op =>
    match op.name, op.args with
    | q`RelRL.rf_and, #[l, r] => top_conjuncts l ++ top_conjuncts r
    | q`RelRL.rf_group, #[r] => top_conjuncts r
    | _, _ => [arg]
  | _ => [arg]

end
end RelRL
end Strata
