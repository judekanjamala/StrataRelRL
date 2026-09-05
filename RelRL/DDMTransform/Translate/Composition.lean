/-
  Copyright StrataRelRL Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module

public import RelRL.DDMTransform.Translate.Projection

namespace Strata
namespace RelRL

public section

open StrataDDM (Arg)

/-! # Both programs at once

The left side keeps its source names and the right is primed, so a relational
formula is an ordinary Core `assert` over both. Every form's binding threading
mirrors its `@[scope(…)]` in `Grammar.lean` — CLAUDE.md, "The other invariant".
`docs/design.md` has each form's lowering and where it comes from in WhyRel.

Imports `Projection.lean` rather than the other way round: a `While` with
alignment guards needs the steps only one side takes, and nothing in a
projection needs the composition. -/

mutual

/-- Lower one bicommand into both programs at once: the left side's statements
under their source names, the right side's primed, emitted in that order per
bicommand — CLAUDE.md, "Emission order is per bicommand". Each branch's binding
threading mirrors that form's `@[scope(…)]` in `Grammar.lean`. -/
partial def compose_bicommand (p : StrataDDM.Program)
    (ictx : Lean.Parser.InputContext) (s : BodyState) (arg : Arg) : TransM BodyState := do
  match arg with
  | .op op =>
    let md := Imperative.MetaData.ofSourceRange (.file ictx.fileName) op.ann
    -- Each side's own range, so a collision points at the declaration.
    let src (a : Arg) : FileRange := { file := .file ictx.fileName, range := a.ann }
    let seq (st : BodyState) (a : Arg) : TransM BodyState := compose_seq p ictx st a
    -- `invariant { R }` clauses, labelled for the verifier's output. Only here:
    -- an invariant is a relational formula, which a projection drops.
    let invariants (st : BodyState) (tag : String) (a : Arg) :
        TransM (List (String × Core.Expression.Expr) × Array Message) := do
      match a with
      | .seq _ _ cs =>
        let mut out : List (String × Core.Expression.Expr) := []
        let mut ds : Array Message := #[]
        let mut i := 0
        for c in cs do
          match c with
          | .op op =>
            match op.args with
            | #[r] =>
              i := i + 1
              let e ← lower_rformula p st.bindings r
              ds := ds ++ check_formula st.declared (src c) e
              out := out ++ [(s!"{tag}_inv_{i}", e)]
            | _ => TransM.error "invariant does not hold exactly one relational formula"
          | _ => TransM.error "invariant is not an operation"
        return (out, ds)
      | _ => TransM.error "invariants are not a sequence"
    match op.name, op.args with
    | q`RelRL.bi_var, #[l, r] =>
      let (ls, b) ← lower_decl_list p s.bindings l
      let (rs, b) ← lower_decl_list p b r
      let s := (s.declare (src l) .left (top_level_declared ls)).declare
                 (src r) .right (top_level_declared rs)
      return { s with
               bindings := b
               out := (s.emit ls (prime_stmts (fragment_names rs) rs)).out }
    | q`RelRL.bi_var_left, #[l] =>
      let (ls, b) ← lower_decl_list p s.bindings l
      let s := s.declare (src l) .left (top_level_declared ls)
      return { (s.emit ls []) with bindings := b }
    | q`RelRL.bi_var_right, #[r] =>
      let (rs, b) ← lower_decl_list p s.bindings r
      let s := s.declare (src r) .right (top_level_declared rs)
      return { s with
               bindings := b
               out := (s.emit [] (prime_stmts (fragment_names rs) rs)).out }
    | q`RelRL.bi_sync, #[c] =>
      -- One statement; `lower_side` takes the sequence a split's side is.
      let (stmts, _) ← lower_side p s.bindings (.seq c.ann .newline #[c])
      let s := { s with diagnostics := s.diagnostics
                   ++ refuse_declarations (src c) "a `|- … -|`" stmts }
      -- One statement, run by both programs, so it must resolve in both.
      let s := (s.check_side (src c) .left stmts).check_side (src c) .right stmts
      return s.emit stmts (prime_stmts (fragment_names stmts) stmts)
    | q`RelRL.bi_call, #[fa, la, ra] =>
      let .ident _ callee := fa
        | TransM.error "synchronized call does not name a procedure"
      match find_biproc p callee with
      | none => return { s with diagnostics := s.diagnostics.push (unknown_callee (src arg) callee) }
      | some callee_op =>
        let lstmt ← lower_call_side p s.bindings fa la
        let rstmt ← lower_call_side p s.bindings fa ra
        let (lwant, rwant) ← match callee_op.args[1]? with
          | some params => biproc_arity s.bindings params
          | none => TransM.error "biproc does not have exactly five arguments"
        let s := { s with diagnostics := s.diagnostics
                     ++ check_call_arity callee .left (src la) lwant (call_counts lstmt)
                     ++ check_call_arity callee .right (src ra) rwant (call_counts rstmt) }
        let s := (s.check_side (src la) .left [lstmt]).check_side (src ra) .right [rstmt]
        -- *One* Core call, not two: the callee's `biproc` became a single
        -- procedure whose inputs are the left side's then the right's, and
        -- whose outputs are likewise — which is the order the two argument
        -- lists concatenate in. So it is the relational contract that is
        -- assumed here, which is the whole point of the form.
        match lstmt, prime_stmts (fragment_names [rstmt]) [rstmt] with
        | .call _ largs _, [.call _ rargs _] =>
          return { s with out := s.out.push (.call callee (largs ++ rargs) md) }
        | _, _ => TransM.error "a synchronized call did not lower to a Core call"
    | q`RelRL.bi_embed, #[l, r] =>
      let (ls, _) ← lower_side p s.bindings l
      let (rs, _) ← lower_side p s.bindings r
      let s := { s with diagnostics := s.diagnostics
                   ++ refuse_declarations (src l) "a split's side" ls
                   ++ refuse_declarations (src r) "a split's side" rs }
      let s := (s.check_side (src l) .left ls).check_side (src r) .right rs
      return s.emit ls (prime_stmts (fragment_names rs) rs)
    | q`RelRL.bi_if, #[lg, rg, thn, els] =>
      let lge ← translateExpr p s.bindings lg
      let rge ← translateExpr p s.bindings rg
      let rge := prime_expr (expr_names rge) rge
      -- Both sides are put under *one* Core `if`, which is faithful only
      -- because the guards are proved to agree first. That obligation is what
      -- WhyRel's rule for `If` requires to align the two branches at all.
      -- Take this `If`'s label before lowering the branches, so a nested one
      -- reads as the later obligation it is.
      let n := s.asserts + 1
      let s := { s with
                 asserts := n
                 diagnostics := s.diagnostics ++ check_formula s.declared (src lg) lge
                   ++ check_formula s.declared (src rg) rge }
      let t ← seq s thn
      let e ← seq (keep s t) els
      let s := keep s e
      let guards := core_app Core.boolEquivOp [lge, rge]
      return { s with
               out := s.out.push (.assert s!"if_guards_{n}" guards md)
                        |>.push (.ite (.det lge) t.out.toList e.out.toList md) }
    | q`RelRL.bi_if4, #[lg, rg, tt, te, et, ee] =>
      -- WhyRel's `Biif4`: the guards need not agree, so there is no agreement
      -- obligation — a branch per combination instead.
      let lge ← translateExpr p s.bindings lg
      let rge ← translateExpr p s.bindings rg
      let rge := prime_expr (expr_names rge) rge
      let s := { s with diagnostics := s.diagnostics
                   ++ check_formula s.declared (src lg) lge
                   ++ check_formula s.declared (src rg) rge }
      let a ← seq s tt
      let b ← seq (keep s a) te
      let c ← seq (keep s b) et
      let d ← seq (keep s c) ee
      let s := keep s d
      let notl := core_app Core.boolNotOp [lge]
      let notr := core_app Core.boolNotOp [rge]
      let inner : Core.Statement :=
        .ite (.det (core_app Core.boolAndOp [notl, rge])) c.out.toList d.out.toList md
      let mid : Core.Statement :=
        .ite (.det (core_app Core.boolAndOp [lge, notr])) b.out.toList [inner] md
      let outer : Core.Statement :=
        .ite (.det (core_app Core.boolAndOp [lge, rge])) a.out.toList [mid] md
      return { s with out := s.out.push outer }
    | q`RelRL.bi_while, #[lg, rg, la, ra, invs, body] =>
      -- WhyRel's general `Biwhile`, from `compile_biwhile` in translate.ml:
      --   while (lg || rg') invariant { align /\ … } {
      --     if (lg && la) then <left projection>
      --     else if (rg' && ra) then <right projection, primed>
      --     else <both sides>
      --   }
      -- The alignment condition is an invariant, not an assert: it is what
      -- rules out a state where one side must step and its guard forbids it.
      let lge ← translateExpr p s.bindings lg
      let rge ← translateExpr p s.bindings rg
      -- The one-sided steps below are this body's projections, and a `biproc`
      -- has no unary contract for one of them to call.
      let s := match bi_call_inside? body with
        | none => s
        | some range =>
          let fr : FileRange := { file := .file ictx.fileName, range := range }
          let d := Message.withRange fr
            "a synchronized `biproc` call cannot appear inside a `While` with \
             alignment guards: the steps only one side takes are this body's \
             projections, and a `biproc` is only ever called by both programs at \
             once. Use the lockstep `While` form, or move the call out of the \
             loop." .userError
          { s with diagnostics := s.diagnostics.push d }
      let rge := prime_expr (expr_names rge) rge
      let lae ← lower_rformula p s.bindings la
      let rae ← lower_rformula p s.bindings ra
      let n := s.asserts + 1
      let s := { s with asserts := n, diagnostics := s.diagnostics
                   ++ check_formula s.declared (src lg) lge
                   ++ check_formula s.declared (src rg) rge
                   ++ check_formula s.declared (src la) lae
                   ++ check_formula s.declared (src ra) rae }
      let (invEs, invDs) ← invariants s s!"while_{n}" invs
      let s := { s with diagnostics := s.diagnostics ++ invDs }
      let lock ← seq s body
      let s := keep s lock
      -- The one-sided steps are this body's projections. Their diagnostics
      -- would repeat the fused pass's, so only that pass's are kept.
      let lonly ← project_seq .left p ictx { s with diagnostics := #[] } body
      let ronly ← project_seq .right p ictx { s with diagnostics := #[] } body
      let ronlyStmts := prime_stmts (fragment_names ronly.out.toList) ronly.out.toList
      let lstep := core_app Core.boolAndOp [lge, lae]
      let rstep := core_app Core.boolAndOp [rge, rae]
      let align := core_app Core.boolOrOp
        [core_app Core.boolOrOp [lstep, rstep],
         core_app Core.boolOrOp
           [core_app Core.boolAndOp [lge, rge],
            core_app Core.boolAndOp
              [core_app Core.boolNotOp [lge], core_app Core.boolNotOp [rge]]]]
      let inner : Core.Statement :=
        .ite (.det lstep) lonly.out.toList
          [.ite (.det rstep) ronlyStmts lock.out.toList md] md
      let loop : Core.Statement :=
        .loop (.det (core_app Core.boolOrOp [lge, rge])) none
          ((s!"while_{n}_align", align) :: invEs) [inner] md
      return { s with out := s.out.push loop }
    | q`RelRL.bi_while_lockstep, #[lg, rg, invs, body] =>
      -- `compile_lockstep_biwhile`: one guard drives both sides, and the
      -- `lockstep` invariant is what makes that faithful.
      let lge ← translateExpr p s.bindings lg
      let rge ← translateExpr p s.bindings rg
      let rge := prime_expr (expr_names rge) rge
      let n := s.asserts + 1
      let s := { s with asserts := n, diagnostics := s.diagnostics
                   ++ check_formula s.declared (src lg) lge
                   ++ check_formula s.declared (src rg) rge }
      let (invEs, invDs) ← invariants s s!"while_{n}" invs
      let s := { s with diagnostics := s.diagnostics ++ invDs }
      let b ← seq s body
      let s := keep s b
      let lockstep := core_app Core.boolEquivOp [lge, rge]
      let loop : Core.Statement :=
        .loop (.det lge) none (invEs ++ [(s!"while_{n}_lockstep", lockstep)])
          b.out.toList md
      return { s with out := s.out.push loop }
    | q`RelRL.bi_while_left, #[g, invs, body] =>
      -- `compile_sided_biwhile`. WhyRel reaches this by writing `Biwhile` with
      -- the other guard false, so one side's guard drives the loop and the body
      -- is the whole bicommand — the user's body is what says the other side
      -- stands still.
      let ge ← translateExpr p s.bindings g
      let n := s.asserts + 1
      let s := { s with
                 asserts := n
                 diagnostics := s.diagnostics ++ check_formula s.declared (src g) ge }
      let (invEs, invDs) ← invariants s s!"while_{n}" invs
      let s := { s with diagnostics := s.diagnostics ++ invDs }
      let b ← seq s body
      let s := keep s b
      return { s with out := s.out.push (.loop (.det ge) none invEs b.out.toList md) }
    | q`RelRL.bi_while_right, #[g, invs, body] =>
      let ge ← translateExpr p s.bindings g
      let ge := prime_expr (expr_names ge) ge
      let n := s.asserts + 1
      let s := { s with
                 asserts := n
                 diagnostics := s.diagnostics ++ check_formula s.declared (src g) ge }
      let (invEs, invDs) ← invariants s s!"while_{n}" invs
      let s := { s with diagnostics := s.diagnostics ++ invDs }
      let b ← seq s body
      let s := keep s b
      return { s with out := s.out.push (.loop (.det ge) none invEs b.out.toList md) }
    | q`RelRL.bi_assert, #[r] =>
      let mut out := s.out
      let mut ds := s.diagnostics
      let mut i := 0
      for conjunct in top_conjuncts r do
        i := i + 1
        let e ← lower_rformula p s.bindings conjunct
        ds := ds ++ check_formula s.declared (src arg) e
        out := out.push (.assert s!"assert_{s.asserts + 1}_{i}" e md)
      return { s with out := out, asserts := s.asserts + 1, diagnostics := ds }
    | q`RelRL.bi_assume, #[r] =>
      -- Same shape as `bi_assert`: it has to observe both sides as they stand,
      -- `Statement.assume` in place of `.assert`.
      let mut out := s.out
      let mut ds := s.diagnostics
      let mut i := 0
      for conjunct in top_conjuncts r do
        i := i + 1
        let e ← lower_rformula p s.bindings conjunct
        ds := ds ++ check_formula s.declared (src arg) e
        out := out.push (.assume s!"assume_{s.assumes + 1}_{i}" e md)
      return { s with out := out, assumes := s.assumes + 1, diagnostics := ds }
    | n, args =>
      TransM.error s!"unexpected bicommand {n.fullName} with {args.size} arguments"
  | _ => TransM.error "biproc body element is not an operation"

/-- Fold a nested sequence into its own accumulator. -/
partial def compose_seq (p : StrataDDM.Program)
    (ictx : Lean.Parser.InputContext) (st : BodyState) (a : Arg) : TransM BodyState := do
  match a with
  | .seq _ _ cs =>
    let mut b : BodyState := { st with out := #[] }
    for c in cs do
      b ← compose_bicommand p ictx b c
    return b
  | _ => TransM.error "expected a sequence of bicommands"

end
end
end RelRL
end Strata
