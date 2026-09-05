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

/-- The Core operator a `Rel` names. The four come from Core's own
`BinaryCmpBaseInt`, so the surface language invents no operator spelling. -/
def bicmp_op (arg : Arg) : TransM Core.Expression.Expr := do
  match arg with
  | .op op =>
    match op.name with
    | q`Core.int_lt => return Core.intLtOp
    | q`Core.int_le => return Core.intLeOp
    | q`Core.int_gt => return Core.intGtOp
    | q`Core.int_ge => return Core.intGeOp
    | n => TransM.error s!"`Rel` does not take {n.fullName}"
  | _ => TransM.error "`Rel`'s comparison is not an operation"

/-- A relational quantifier's binders, the left list first — the order
`Grammar.lean`'s `@[scope]` chain puts them in, and so the Core binder order.
A shared list is one binder both readings see. -/
def bi_quant_decls (bindings : TransBindings) (arg : Arg) :
    TransM (ListMap Core.Expression.Ident Lambda.LTy) := do
  match arg with
  | .op op =>
    match op.name, op.args with
    | q`RelRL.biq_both, #[l, r] =>
      return (← translateDeclList bindings l) ++ (← translateDeclList bindings r)
    | q`RelRL.biq_left, #[l] => translateDeclList bindings l
    | q`RelRL.biq_right, #[r] => translateDeclList bindings r
    | q`RelRL.biq_shared, #[x] => translateDeclList bindings x
    | n, args =>
      TransM.error s!"unexpected quantifier bindings {n.fullName} with {args.size} arguments"
  | _ => TransM.error "quantifier bindings are not an operation"

mutual

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
    | q`RelRL.rf_bicmp, #[f, l, r] =>
      let op ← bicmp_op f
      let l ← translateExpr p bindings l
      let r ← translateExpr p bindings r
      return bool_app op [l, prime_expr (expr_names r) r]
    | q`RelRL.rf_forall, #[xs, b] => lower_quant .all p bindings xs b
    | q`RelRL.rf_exists, #[xs, b] => lower_quant .exist p bindings xs b
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

/-- One Core quantifier per binder, the left list outermost, over the lowered
body. The binders extend `bindings` exactly as `@[scope(xs)]` extends the scope
chain — CLAUDE.md, "The other invariant". Core's `withScopedBindings` is the
shape mirrored here; it cannot be reused, since the body is a relational
formula rather than a Core expression.

A binder is a Core *bound* variable, which is what keeps priming off it:
`prime_expr` renames free variables, and this is not one. -/
partial def lower_quant (qk : Lambda.QuantifierKind) (p : StrataDDM.Program)
    (bindings : TransBindings) (xsa ba : Arg) : TransM Core.Expression.Expr := do
  let xs ← bi_quant_decls bindings xsa
  let n := xs.length
  let bound := (xs.mapIdx (fun i _ => Lambda.LExpr.bvar () (n - 1 - i))).toArray
  let b ← lower_rformula p { bindings with boundVars := bindings.boundVars ++ bound } ba
  xs.foldrM (init := b) fun (name, ty) e =>
    match ty with
    | .forAll [] mty =>
      return .quant () qk name.name (.some mty) (Lambda.LExpr.noTrigger ()) e
    | _ => TransM.error s!"a relational quantifier binds `{name.name}` at a polymorphic type"

end

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
