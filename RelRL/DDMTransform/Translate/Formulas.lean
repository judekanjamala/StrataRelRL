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

/-- Apply one of Core's operators. A relational formula has no Core surface
syntax to route through `translateFnTable`, so it builds the same applications
directly. -/
def core_app (op : Core.Expression.Expr) (args : List Core.Expression.Expr) :
    Core.Expression.Expr :=
  Lambda.LExpr.mkApp () op args

/-- The Core operator one of Core's own int-operator categories names. `Rel`
and `BiExp` take those categories directly, so the surface language invents no
operator spelling and gains one the moment Core does. -/
def int_op (arg : Arg) : TransM Core.Expression.Expr := do
  match arg with
  | .op op =>
    match op.name with
    | q`Core.int_lt => return Core.intLtOp
    | q`Core.int_le => return Core.intLeOp
    | q`Core.int_gt => return Core.intGtOp
    | q`Core.int_ge => return Core.intGeOp
    | q`Core.int_add => return Core.intAddOp
    | q`Core.int_sub => return Core.intSubOp
    | q`Core.int_mul => return Core.intMulOp
    | q`Core.int_div => return Core.intDivOp
    | q`Core.int_mod => return Core.intModOp
    | q`Core.int_neg => return Core.intNegOp
    | n => TransM.error s!"no Core operator for {n.fullName}"
  | _ => TransM.error "an operator slot is not an operation"

/-- A bi-expression. `[< e <]` reads the left state and `[> e >]` the right,
which is the primed reading as everywhere else; the arithmetic above them is
what lets one term mix the two. -/
partial def lower_biexp (p : StrataDDM.Program) (bindings : TransBindings)
    (arg : Arg) : TransM Core.Expression.Expr := do
  match arg with
  | .op op =>
    match op.name, op.args with
    | q`RelRL.be_left, #[e] => translateExpr p bindings e
    | q`RelRL.be_right, #[e] =>
      let e ← translateExpr p bindings e
      return prime_expr (expr_names e) e
    | q`RelRL.be_arith, #[f, l, r]
    | q`RelRL.be_divmod, #[f, l, r] =>
      return core_app (← int_op f)
        [← lower_biexp p bindings l, ← lower_biexp p bindings r]
    | q`RelRL.be_neg, #[f, e] =>
      return core_app (← int_op f) [← lower_biexp p bindings e]
    | n, args =>
      TransM.error s!"unexpected bi-expression {n.fullName} with {args.size} arguments"
  | _ => TransM.error "bi-expression is not an operation"

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

/-- A `Let`'s bindings, outermost first: the declared name with its type, the
value, and whether that value is read in the right state. -/
partial def bi_let_binds (arg : Arg) : TransM (List (Arg × String × Arg × Bool)) := do
  match arg with
  | .op op =>
    match op.name, op.args with
    | q`RelRL.biletAtom, #[b] => bi_let_binds b
    | q`RelRL.biletPush, #[bs, b] => return (← bi_let_binds bs) ++ (← bi_let_binds b)
    | q`RelRL.bilet_left, #[tp, .ident _ x, e] => return [(tp, x, e, false)]
    | q`RelRL.bilet_right, #[tp, .ident _ x, e] => return [(tp, x, e, true)]
    | n, args =>
      TransM.error s!"unexpected `Let` binding {n.fullName} with {args.size} arguments"
  | _ => TransM.error "`Let` bindings are not an operation"

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
    | q`RelRL.rf_bicmp_exp, #[f, l, r] =>
      return core_app (← int_op f)
        [← lower_biexp p bindings l, ← lower_biexp p bindings r]
    | q`RelRL.rf_let, #[bs, b] => lower_bilet p bindings bs b
    | q`RelRL.rf_forall, #[xs, b] => lower_quant .all p bindings xs b
    | q`RelRL.rf_exists, #[xs, b] => lower_quant .exist p bindings xs b
    | q`RelRL.rf_group, #[r] =>
      lower_rformula p bindings r
    | q`RelRL.rf_not, #[r] =>
      return core_app Core.boolNotOp [← lower_rformula p bindings r]
    | q`RelRL.rf_and, #[l, r] =>
      return core_app Core.boolAndOp
        [← lower_rformula p bindings l, ← lower_rformula p bindings r]
    | q`RelRL.rf_or, #[l, r] =>
      return core_app Core.boolOrOp
        [← lower_rformula p bindings l, ← lower_rformula p bindings r]
    | q`RelRL.rf_implies, #[l, r] =>
      return core_app Core.boolImpliesOp
        [← lower_rformula p bindings l, ← lower_rformula p bindings r]
    | q`RelRL.rf_iff, #[l, r] =>
      return core_app Core.boolEquivOp
        [← lower_rformula p bindings l, ← lower_rformula p bindings r]
    | n, args =>
      TransM.error s!"unexpected relational formula {n.fullName} with {args.size} arguments"
  | _ => TransM.error "relational formula is not an operation"

/-- WhyRel's `Rlet`, as a chain of Core `have`s. Each value is read in its own
side — `[> e >]` primed, `[< e <]` not — in the scope of the bindings before it,
and the body under all of them.

This is where every Core expression reaches across the two programs: the names
are Core bound variables, so nothing primes them and the body may combine values
from the two sides at any type, with Core's own operators. `docs/design.md` on
why that is the general mechanism rather than a `BiExp` copy of Core's grammar. -/
partial def lower_bilet (p : StrataDDM.Program) (bindings : TransBindings)
    (bsa ba : Arg) : TransM Core.Expression.Expr := do
  let items ← bi_let_binds bsa
  -- A `.bvar` counts from the innermost binder, so each prefix is numbered on
  -- its own — the shape of Core's `withScopedBindings`, one step at a time.
  let scope (k : Nat) : TransBindings :=
    { bindings with boundVars := bindings.boundVars ++
        ((List.range k).map (fun i => Lambda.LExpr.bvar () (k - 1 - i))).toArray }
  let mut vals := []
  for (tpa, name, ea, right) in items do
    let ty ← translateLMonoTy bindings tpa
    let v ← translateExpr p (scope vals.length) ea
    vals := vals ++ [(name, ty, if right then prime_expr (expr_names v) v else v)]
  let body ← lower_rformula p (scope items.length) ba
  return vals.foldr (fun (name, ty, v) e => Lambda.LExpr.mkHave () name (.some ty) v e) body

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
