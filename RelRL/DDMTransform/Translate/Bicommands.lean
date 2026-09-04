/-
  Copyright StrataRelRL Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module

public import RelRL.DDMTransform.Translate.Formulas
public import RelRL.DDMTransform.Translate.State
public import Strata.Languages.Core.Verifier
public import Strata.DL.Imperative.MetaData
public import Strata.Pipeline.Messages
import StrataDDM.AST

namespace Strata
namespace RelRL

public section

open StrataDDM (Arg)

/-! # Lowering one bicommand

`lower_bicommand` is the fold over a `biproc` body. Every form's binding
threading mirrors its `@[scope(…)]` in `Grammar.lean` — CLAUDE.md, "The other
invariant" — and the compound forms recur through `seq_body`. `docs/design.md`
has each form's lowering and where it comes from in WhyRel. -/

/-- Lower one side's statements. The synthetic `Core.block` wrap is all
`translateBlock` needs; `bindings` is the scope the side was elaborated in. -/
def lower_side (p : StrataDDM.Program) (bindings : TransBindings) (arg : Arg) :
    TransM (List Core.Statement × TransBindings) := do
  match arg with
  | .seq ann _ stmts =>
    translateBlock p bindings
      (.op { ann, name := q`Core.block, args := #[.seq ann .newline stmts] })
  | _ => TransM.error "bicommand side is not a statement sequence"

/-- Lower a `Var` side's `DeclList`, by putting it back in the
`Core.varStatement` Core's grammar wraps it in. Nothing is initialized. -/
def lower_decl_list (p : StrataDDM.Program) (bindings : TransBindings) (dl : Arg) :
    TransM (List Core.Statement × TransBindings) := do
  let ann := dl.ann
  let stmt : Arg := .op { ann, name := q`Core.varStatement, args := #[.option ann none, dl] }
  translateBlock p bindings
    (.op { ann, name := q`Core.block, args := #[.seq ann .newline #[stmt]] })


/-- The `biproc` a synchronized call names, if this file declares one. A unary
`procedure` is not one: it is called from inside a side, through Core's `call`.
-/
def find_biproc (p : StrataDDM.Program) (name : String) : Option StrataDDM.Operation :=
  p.commands.find? fun op =>
    op.name == q`RelRL.biproc &&
      (match (op.args[0]? : Option Arg) with
       | some (.ident _ n) => n == name
       | _ => false)

/-- One side of a synchronized call, lowered by putting it back in the
`Core.call_statement` Core's grammar wraps it in — so `out`/`inout` arguments go
through Core's own translator rather than a second copy of it here. -/
def lower_call_side (p : StrataDDM.Program) (bindings : TransBindings)
    (name : Arg) (args : Arg) : TransM Core.Statement := do
  let ann := args.ann
  let stmt : Arg := .op { ann, name := q`Core.call_statement,
                          args := #[.option ann none, name, args] }
  match ← translateStmt p bindings stmt with
  | ([st], _) => return st
  | _ => TransM.error "a call statement did not lower to exactly one Core statement"

/-- The callee's parameter counts, per side: value arguments, then results. An
`inout` counts as both, exactly as it does at the call site. -/
def biproc_arity (bindings : TransBindings) (params : Arg) :
    TransM ((Nat × Nat) × (Nat × Nat)) := do
  match params with
  | .option _ none => return ((0, 0), (0, 0))
  | .option _ (some (.op op)) =>
    match op.args with
    | #[l, r] =>
      let (li, lo, b) ← translateProcBindings bindings l
      let (ri, ro, _) ← translateProcBindings b r
      return ((li.length, lo.length), (ri.length, ro.length))
    | _ => TransM.error "biproc parameters are not a left/right pair"
  | _ => TransM.error "biproc parameters are not an option"

/-- How many arguments and results a lowered call passes. -/
def call_counts : Core.Statement → Nat × Nat
  | .call _ args _ =>
    ((Core.CallArg.getInputExprs args).length, (Core.CallArg.getLhs args).length)
  | _ => (0, 0)

/-- Check one side's argument list against the callee's parameters. Core checks
this too, but only after the two sides have been fused into one argument list,
so its message names neither the side nor a source position. -/
def check_call_arity (callee : String) (side : Side) (fr : FileRange)
    (want got : Nat × Nat) : Array Message :=
  if want == got then #[] else
    #[Message.withRange fr
        s!"`{callee}`'s {side.name} side takes {want.1} argument(s) and {want.2} \
           result(s); this call passes {got.1} and {got.2}" .userError]

/-- Refuse a Core declaration anywhere inside a side — nested in an `if` or
`while` body included. `Var` is the only form that declares, as in WhyRel, whose
`|_ … _|` takes an `atomic_command` and whose only binder is `Var … in CC`.

Nesting is refused rather than left alone because it is not actually safe: two
sibling blocks declaring one name make Core drop every obligation in the
procedure, silently and with exit 0 — [`issues.md`](issues.md), "Sibling blocks
sharing a declared name lose every obligation". Each bicommand emits into one
flat block, so two bicommands' `if`s are siblings and one repeated name reaches
it. -/
def refuse_declarations (fr : FileRange) (what : String)
    (stmts : List Core.Statement) : Array Message :=
  let declared := (Imperative.HasVarsImp.definedVars (P := Core.Expression) stmts false)
    |>.map (·.name) |>.eraseDups
  declared.foldl (init := #[]) fun ds name =>
    ds.push <| Message.withRange fr
      s!"`{name}` cannot be declared inside {what}: `Var` is the only form that \
         declares. Write `Var {name} : … | … ;` before the bicommand." .userError

/-- Where a synchronized `biproc` call sits inside a bicommand tree, if one
does. `bi_while` lowers its body through `.project` to get the steps only one
side takes, and a `biproc` has no unary contract for those steps to call —
`docs/status.md` says what to write instead. -/
partial def bi_call_inside? (a : Arg) : Option StrataDDM.SourceRange :=
  match a with
  | .op op =>
    if op.name == q`RelRL.bi_call then some op.ann else op.args.findSome? bi_call_inside?
  | .seq _ _ as => as.findSome? bi_call_inside?
  | .option _ (some b) => bi_call_inside? b
  | _ => none

/-- Lower one bicommand, extending the accumulator. Each branch's binding
threading mirrors that form's `@[scope(…)]` in `Grammar.lean`. Under `project`,
one side is kept verbatim and nothing is primed or checked for collisions —
there is only one program, and Core checks it directly. -/
partial def lower_bicommand (mode : Mode) (p : StrataDDM.Program)
    (ictx : Lean.Parser.InputContext) (s : BodyState) (arg : Arg) : TransM BodyState := do
  match arg with
  | .op op =>
    let md := Imperative.MetaData.ofSourceRange (.file ictx.fileName) op.ann
    -- Each side's own range, so a collision points at the declaration.
    let src (a : Arg) : FileRange := { file := .file ictx.fileName, range := a.ann }
    -- A nested bicommand sequence, lowered into its own accumulator: its
    -- declarations are scoped to the Core block it becomes, so `declared` does
    -- not come back out. Counters do, to keep labels unique body-wide. `m` is
    -- a parameter because a `While` with alignment guards lowers its body three
    -- times — fused, and once per side, for the steps only one side takes.
    let seq_body (m : Mode) (st : BodyState) (a : Arg) : TransM BodyState := do
      match a with
      | .seq _ _ cs =>
        let mut b : BodyState := { st with out := #[] }
        for c in cs do
          b ← lower_bicommand m p ictx b c
        return b
      | _ => TransM.error "expected a sequence of bicommands"
    let keep (outer : BodyState) (b : BodyState) : BodyState :=
      { outer with asserts := b.asserts, assumes := b.assumes, diagnostics := b.diagnostics }
    -- `invariant { R }` clauses, labelled for the verifier's output.
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
      let rnames := top_level_declared rs
      match mode with
      | .compose =>
        let s := (s.declare (src l) .left (top_level_declared ls)).declare (src r) .right rnames
        return { s with
                 bindings := b
                 out := (s.emit ls (prime_stmts (fragment_names rs) rs)).out }
      | .project .left => return { (s.emit ls []) with bindings := b }
      | .project .right => return { (s.emit rs []) with bindings := b }
    | q`RelRL.bi_var_left, #[l] =>
      let (ls, b) ← lower_decl_list p s.bindings l
      match mode with
      | .project .right => return { s with bindings := b }
      | .project .left => return { (s.emit ls []) with bindings := b }
      | .compose =>
        let s := s.declare (src l) .left (top_level_declared ls)
        return { (s.emit ls []) with bindings := b }
    | q`RelRL.bi_var_right, #[r] =>
      let (rs, b) ← lower_decl_list p s.bindings r
      let rnames := top_level_declared rs
      match mode with
      | .compose =>
        let s := s.declare (src r) .right rnames
        return { s with
                 bindings := b
                 out := (s.emit [] (prime_stmts (fragment_names rs) rs)).out }
      | .project .right => return { (s.emit rs []) with bindings := b }
      | .project .left => return { s with bindings := b }
    | q`RelRL.bi_sync, #[c] =>
      -- One statement; `lower_side` takes the sequence a split's side is.
      let (stmts, _) ← lower_side p s.bindings (.seq c.ann .newline #[c])
      let s := { s with diagnostics := s.diagnostics
                   ++ refuse_declarations (src c) "a `|- … -|`" stmts }
      match mode with
      | .compose =>
        -- One statement, run by both programs, so it must resolve in both.
        let s := (s.check_side (src c) .left stmts).check_side (src c) .right stmts
        return s.emit stmts (prime_stmts (fragment_names stmts) stmts)
      | .project _ => return s.emit stmts []
    | q`RelRL.bi_call, #[fa, la, ra] =>
      let .ident _ callee := fa
        | TransM.error "synchronized call does not name a procedure"
      match find_biproc p callee with
      | none =>
        let d := Message.withRange (src arg)
          s!"`{callee}` is not a `biproc` declared in this file. A unary \
             `procedure` is called from inside a side — `|- call {callee}(…); -| ;` \
             — and relates the two programs through its own spec." .userError
        return { s with diagnostics := s.diagnostics.push d }
      | some callee_op =>
        let lstmt ← lower_call_side p s.bindings fa la
        let rstmt ← lower_call_side p s.bindings fa ra
        let (lwant, rwant) ← match callee_op.args[1]? with
          | some params => biproc_arity s.bindings params
          | none => TransM.error "biproc does not have exactly five arguments"
        let s := { s with diagnostics := s.diagnostics
                     ++ check_call_arity callee .left (src la) lwant (call_counts lstmt)
                     ++ check_call_arity callee .right (src ra) rwant (call_counts rstmt) }
        match mode with
        | .project .left => return s.emit [lstmt] []
        | .project .right => return s.emit [rstmt] []
        | .compose =>
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
      let side_of (a : Arg) (stmts : List Core.Statement) : Array Message :=
        refuse_declarations (src a) "a split's side" stmts
      match mode with
      | .compose =>
        let (ls, _) ← lower_side p s.bindings l
        let (rs, _) ← lower_side p s.bindings r
        let s := { s with diagnostics := s.diagnostics ++ side_of l ls ++ side_of r rs }
        let s := (s.check_side (src l) .left ls).check_side (src r) .right rs
        return s.emit ls (prime_stmts (fragment_names rs) rs)
      | .project .left =>
        let (ls, _) ← lower_side p s.bindings l
        return { (s.emit ls []) with diagnostics := s.diagnostics ++ side_of l ls }
      | .project .right =>
        let (rs, _) ← lower_side p s.bindings r
        return { (s.emit rs []) with diagnostics := s.diagnostics ++ side_of r rs }
    | q`RelRL.bi_if_then, #[lg, rg, thn] =>
      -- WhyRel desugars the else-less form to an empty else; so does this, by
      -- passing an empty sequence on to the same branch.
      lower_bicommand mode p ictx s
        (.op { ann := op.ann, name := q`RelRL.bi_if,
               args := #[lg, rg, thn, .seq op.ann .newline #[]] })
    | q`RelRL.bi_if, #[lg, rg, thn, els] =>
      match mode with
      | .compose =>
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
        let t ← seq_body mode s thn
        let e ← seq_body mode (keep s t) els
        let s := keep s e
        let guards := bool_app Core.boolEquivOp [lge, rge]
        return { s with
                 out := s.out.push (.assert s!"if_guards_{n}" guards md)
                          |>.push (.ite (.det lge) t.out.toList e.out.toList md) }
      | .project side =>
        let g ← translateExpr p s.bindings (match side with | .left => lg | .right => rg)
        let t ← seq_body mode s thn
        let e ← seq_body mode (keep s t) els
        let s := keep s e
        return { s with out := s.out.push (.ite (.det g) t.out.toList e.out.toList md) }
    | q`RelRL.bi_if4, #[lg, rg, tt, te, et, ee] =>
      -- WhyRel's `Biif4`: the guards need not agree, so there is no agreement
      -- obligation — a branch per combination instead.
      let lge ← translateExpr p s.bindings lg
      let rge ← translateExpr p s.bindings rg
      match mode with
      | .compose =>
        let rge := prime_expr (expr_names rge) rge
        let s := { s with diagnostics := s.diagnostics
                     ++ check_formula s.declared (src lg) lge
                     ++ check_formula s.declared (src rg) rge }
        let a ← seq_body mode s tt
        let b ← seq_body mode (keep s a) te
        let c ← seq_body mode (keep s b) et
        let d ← seq_body mode (keep s c) ee
        let s := keep s d
        let notl := bool_app Core.boolNotOp [lge]
        let notr := bool_app Core.boolNotOp [rge]
        let inner : Core.Statement :=
          .ite (.det (bool_app Core.boolAndOp [notl, rge])) c.out.toList d.out.toList md
        let mid : Core.Statement :=
          .ite (.det (bool_app Core.boolAndOp [lge, notr])) b.out.toList [inner] md
        let outer : Core.Statement :=
          .ite (.det (bool_app Core.boolAndOp [lge, rge])) a.out.toList [mid] md
        return { s with out := s.out.push outer }
      | .project side =>
        -- `annot.ml`'s `projl`/`projr`: one side's guard picks between the two
        -- branches that agree on that side — then-then against else-then on the
        -- left, then-then against then-else on the right.
        let (g, thn, els) := match side with
          | .left => (lge, tt, et)
          | .right => (rge, tt, te)
        let a ← seq_body mode s thn
        let b ← seq_body mode (keep s a) els
        let s := keep s b
        return { s with out := s.out.push (.ite (.det g) a.out.toList b.out.toList md) }
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
      match mode with
      | .compose =>
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
        let lock ← seq_body .compose s body
        let s := keep s lock
        -- The one-sided steps are this body's projections. Their diagnostics
        -- would repeat the fused pass's, so only that pass's are kept.
        let lonly ← seq_body (.project .left) { s with diagnostics := #[] } body
        let ronly ← seq_body (.project .right) { s with diagnostics := #[] } body
        let ronlyStmts := prime_stmts (fragment_names ronly.out.toList) ronly.out.toList
        let lstep := bool_app Core.boolAndOp [lge, lae]
        let rstep := bool_app Core.boolAndOp [rge, rae]
        let align := bool_app Core.boolOrOp
          [bool_app Core.boolOrOp [lstep, rstep],
           bool_app Core.boolOrOp
             [bool_app Core.boolAndOp [lge, rge],
              bool_app Core.boolAndOp
                [bool_app Core.boolNotOp [lge], bool_app Core.boolNotOp [rge]]]]
        let inner : Core.Statement :=
          .ite (.det lstep) lonly.out.toList
            [.ite (.det rstep) ronlyStmts lock.out.toList md] md
        let loop : Core.Statement :=
          .loop (.det (bool_app Core.boolOrOp [lge, rge])) none
            ((s!"while_{n}_align", align) :: invEs) [inner] md
        return { s with out := s.out.push loop }
      | .project side =>
        let b ← seq_body mode s body
        let s := keep s b
        let g := match side with | .left => lge | .right => rge
        return { s with out := s.out.push (.loop (.det g) none [] b.out.toList md) }
    | q`RelRL.bi_while_lockstep, #[lg, rg, invs, body] =>
      -- `compile_lockstep_biwhile`: one guard drives both sides, and the
      -- `lockstep` invariant is what makes that faithful.
      let lge ← translateExpr p s.bindings lg
      let rge ← translateExpr p s.bindings rg
      match mode with
      | .compose =>
        let rge := prime_expr (expr_names rge) rge
        let n := s.asserts + 1
        let s := { s with asserts := n, diagnostics := s.diagnostics
                     ++ check_formula s.declared (src lg) lge
                     ++ check_formula s.declared (src rg) rge }
        let (invEs, invDs) ← invariants s s!"while_{n}" invs
        let s := { s with diagnostics := s.diagnostics ++ invDs }
        let b ← seq_body mode s body
        let s := keep s b
        let lockstep := bool_app Core.boolEquivOp [lge, rge]
        let loop : Core.Statement :=
          .loop (.det lge) none (invEs ++ [(s!"while_{n}_lockstep", lockstep)])
            b.out.toList md
        return { s with out := s.out.push loop }
      | .project side =>
        let b ← seq_body mode s body
        let s := keep s b
        let g := match side with | .left => lge | .right => rge
        return { s with out := s.out.push (.loop (.det g) none [] b.out.toList md) }
    | q`RelRL.bi_while_left, #[g, invs, body] =>
      -- `compile_sided_biwhile`. WhyRel reaches this by writing `Biwhile` with
      -- the other guard false, so one side's guard drives the loop and the body
      -- is the whole bicommand — the user's body is what says the other side
      -- stands still. Projecting onto the *other* side gives `while false`,
      -- which is emitted as nothing.
      let ge ← translateExpr p s.bindings g
      match mode with
      | .compose =>
        let n := s.asserts + 1
        let s := { s with
                   asserts := n
                   diagnostics := s.diagnostics ++ check_formula s.declared (src g) ge }
        let (invEs, invDs) ← invariants s s!"while_{n}" invs
        let s := { s with diagnostics := s.diagnostics ++ invDs }
        let b ← seq_body mode s body
        let s := keep s b
        return { s with out := s.out.push (.loop (.det ge) none invEs b.out.toList md) }
      | .project .right => return s
      | .project .left =>
        let b ← seq_body mode s body
        let s := keep s b
        return { s with out := s.out.push (.loop (.det ge) none [] b.out.toList md) }
    | q`RelRL.bi_while_right, #[g, invs, body] =>
      let ge ← translateExpr p s.bindings g
      match mode with
      | .compose =>
        let ge := prime_expr (expr_names ge) ge
        let n := s.asserts + 1
        let s := { s with
                   asserts := n
                   diagnostics := s.diagnostics ++ check_formula s.declared (src g) ge }
        let (invEs, invDs) ← invariants s s!"while_{n}" invs
        let s := { s with diagnostics := s.diagnostics ++ invDs }
        let b ← seq_body mode s body
        let s := keep s b
        return { s with out := s.out.push (.loop (.det ge) none invEs b.out.toList md) }
      | .project .left => return s
      | .project .right =>
        let b ← seq_body mode s body
        let s := keep s b
        return { s with out := s.out.push (.loop (.det ge) none [] b.out.toList md) }
    | q`RelRL.bi_assert, #[r] =>
      match mode with
      | .project _ => return s
      | .compose =>
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
      match mode with
      | .project _ => return s
      | .compose =>
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

end
end RelRL
end Strata
