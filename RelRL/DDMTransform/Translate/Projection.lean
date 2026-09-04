/-
  Copyright StrataRelRL Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module

public import RelRL.DDMTransform.Translate.Sides

namespace Strata
namespace RelRL

public section

open StrataDDM (Arg)

/-! # One side alone

`docs/design.md` argues the choices; `Sides.lean` holds what this shares with
`Composition.lean`. -/

mutual

/-- Lower one bicommand onto `side` alone. There is one program here, so nothing
is primed and nothing is checked for collisions — Core checks the result
directly — and every relational formula is dropped, since it names both sides
and says nothing about one. What survives is the side's own statements, in
order.

Not only a printing aid: `compose_bicommand`'s `bi_while` lowers its body
through this to get the steps only one side takes. -/
partial def project_bicommand (side : Side) (p : StrataDDM.Program)
    (ictx : Lean.Parser.InputContext) (s : BodyState) (arg : Arg) : TransM BodyState := do
  match arg with
  | .op op =>
    let md := Imperative.MetaData.ofSourceRange (.file ictx.fileName) op.ann
    let src (a : Arg) : FileRange := { file := .file ictx.fileName, range := a.ann }
    let seq (st : BodyState) (a : Arg) : TransM BodyState := project_seq side p ictx st a
    match op.name, op.args with
    -- Both sides are lowered even though one is dropped: `Var` extends the
    -- scope, and the chain has to advance the same way it does under compose or
    -- a later de Bruijn index resolves against the wrong binding.
    | q`RelRL.bi_var, #[l, r] =>
      let (ls, b) ← lower_decl_list p s.bindings l
      let (rs, b) ← lower_decl_list p b r
      return { (s.emit (match side with | .left => ls | .right => rs) []) with bindings := b }
    | q`RelRL.bi_var_left, #[l] =>
      let (ls, b) ← lower_decl_list p s.bindings l
      match side with
      | .left => return { (s.emit ls []) with bindings := b }
      | .right => return { s with bindings := b }
    | q`RelRL.bi_var_right, #[r] =>
      let (rs, b) ← lower_decl_list p s.bindings r
      match side with
      | .right => return { (s.emit rs []) with bindings := b }
      | .left => return { s with bindings := b }
    | q`RelRL.bi_sync, #[c] =>
      let (stmts, _) ← lower_side p s.bindings (.seq c.ann .newline #[c])
      let s := { s with diagnostics := s.diagnostics
                   ++ refuse_declarations (src c) "a `|- … -|`" stmts }
      return s.emit stmts []
    | q`RelRL.bi_call, #[fa, la, ra] =>
      let .ident _ callee := fa
        | TransM.error "synchronized call does not name a procedure"
      match find_biproc p callee with
      | none => return { s with diagnostics := s.diagnostics.push (unknown_callee (src arg) callee) }
      | some callee_op =>
        -- Both sides are lowered so the arity of each is still reported: the
        -- program is ill-formed whichever side is being printed.
        let lstmt ← lower_call_side p s.bindings fa la
        let rstmt ← lower_call_side p s.bindings fa ra
        let (lwant, rwant) ← match callee_op.args[1]? with
          | some params => biproc_arity s.bindings params
          | none => TransM.error "biproc does not have exactly five arguments"
        let s := { s with diagnostics := s.diagnostics
                     ++ check_call_arity callee .left (src la) lwant (call_counts lstmt)
                     ++ check_call_arity callee .right (src ra) rwant (call_counts rstmt) }
        return s.emit [match side with | .left => lstmt | .right => rstmt] []
    | q`RelRL.bi_embed, #[l, r] =>
      -- A split's sides declare nothing that outlives them, so only the kept
      -- one is lowered.
      let a := match side with | .left => l | .right => r
      let (stmts, _) ← lower_side p s.bindings a
      return { (s.emit stmts []) with
               diagnostics := s.diagnostics ++ refuse_declarations (src a) "a split's side" stmts }
    | q`RelRL.bi_if, #[lg, rg, thn, els] =>
      let g ← translateExpr p s.bindings (match side with | .left => lg | .right => rg)
      let t ← seq s thn
      let e ← seq (keep s t) els
      let s := keep s e
      return { s with out := s.out.push (.ite (.det g) t.out.toList e.out.toList md) }
    | q`RelRL.bi_if4, #[lg, rg, tt, te, et, _ee] =>
      -- `annot.ml`'s `projl`/`projr`: one side's guard picks between the two
      -- branches that agree on that side — then-then against else-then on the
      -- left, then-then against then-else on the right.
      let lge ← translateExpr p s.bindings lg
      let rge ← translateExpr p s.bindings rg
      let (g, thn, els) := match side with
        | .left => (lge, tt, et)
        | .right => (rge, tt, te)
      let a ← seq s thn
      let b ← seq (keep s a) els
      let s := keep s b
      return { s with out := s.out.push (.ite (.det g) a.out.toList b.out.toList md) }
    | q`RelRL.bi_while, #[lg, rg, _la, _ra, _invs, body] =>
      let lge ← translateExpr p s.bindings lg
      let rge ← translateExpr p s.bindings rg
      let b ← seq s body
      let s := keep s b
      let g := match side with | .left => lge | .right => rge
      return { s with out := s.out.push (.loop (.det g) none [] b.out.toList md) }
    | q`RelRL.bi_while_lockstep, #[lg, rg, _invs, body] =>
      let lge ← translateExpr p s.bindings lg
      let rge ← translateExpr p s.bindings rg
      let b ← seq s body
      let s := keep s b
      let g := match side with | .left => lge | .right => rge
      return { s with out := s.out.push (.loop (.det g) none [] b.out.toList md) }
    -- Projecting a one-sided loop onto the *other* side gives `while false`,
    -- which is emitted as nothing.
    | q`RelRL.bi_while_left, #[g, _invs, body] =>
      let ge ← translateExpr p s.bindings g
      match side with
      | .right => return s
      | .left =>
        let b ← seq s body
        let s := keep s b
        return { s with out := s.out.push (.loop (.det ge) none [] b.out.toList md) }
    | q`RelRL.bi_while_right, #[g, _invs, body] =>
      let ge ← translateExpr p s.bindings g
      match side with
      | .left => return s
      | .right =>
        let b ← seq s body
        let s := keep s b
        return { s with out := s.out.push (.loop (.det ge) none [] b.out.toList md) }
    -- Relational, so there is nothing here for one program alone.
    | q`RelRL.bi_assert, #[_] => return s
    | q`RelRL.bi_assume, #[_] => return s
    | n, args =>
      TransM.error s!"unexpected bicommand {n.fullName} with {args.size} arguments"
  | _ => TransM.error "biproc body element is not an operation"

/-- Fold a nested sequence into its own accumulator. -/
partial def project_seq (side : Side) (p : StrataDDM.Program)
    (ictx : Lean.Parser.InputContext) (st : BodyState) (a : Arg) : TransM BodyState := do
  match a with
  | .seq _ _ cs =>
    let mut b : BodyState := { st with out := #[] }
    for c in cs do
      b ← project_bicommand side p ictx b c
    return b
  | _ => TransM.error "expected a sequence of bicommands"

end
end
end RelRL
end Strata
