/-
  Copyright StrataRelRL Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module

public import Strata.Languages.Core.DDMTransform.Grammar
public import StrataDDM.HNF
public import StrataDDM.Integration.Lean.OfAstM
import StrataDDM.Integration.Lean -- shake: keep

public section

namespace Strata

#dialect
dialect RelRL;
import Core;

// Surface syntax follows WhyRel (dnaumann/RelRL, src/parser/parser.mly);
// statements inside a side are Core's. Every deviation, and every scoping
// decision below, is argued in docs/design.md.
//
// Editing this file: the `@[scope(...)]` chain below is mirrored by hand in
// Translate.lean. CLAUDE.md, "The other invariant", says what breaks if they
// drift.

// ---- Relational formulas ----------------------------------------------
// `<| p <]` reads p in the left state, `[> p |>` in the right; `l =:= r`
// relates a left expression to a right one; `Agree x` is `x =:= x`; `Both (p)`
// is `<| p <] /\ [> p |>`.
category RFormula;

op rf_agree (x : Ident) : RFormula => "Agree " x;
op rf_both (p : bool) : RFormula => "Both (" p ")";
op rf_left (p : bool) : RFormula => "<| " p " <]";
op rf_right (p : bool) : RFormula => "[> " p " |>";
op rf_biequal (tp : Type, l : tp, r : tp) : RFormula => @[prec(15)] l " =:= " r;
op rf_group (r : RFormula) : RFormula => "{ " r " }";
op rf_not (r : RFormula) : RFormula => @[prec(20)] "~ " r;
op rf_and (l : RFormula, r : RFormula) : RFormula => @[prec(10), leftassoc] l " /\\ " r;
op rf_or (l : RFormula, r : RFormula) : RFormula => @[prec(8), leftassoc] l " \\/ " r;
op rf_implies (l : RFormula, r : RFormula) : RFormula => @[prec(5), rightassoc] l " => " r;
op rf_iff (l : RFormula, r : RFormula) : RFormula => @[prec(4)] l " <=> " r;

// ---- Bicommands -------------------------------------------------------
// Only `bi_var` and `bi_sync` declare, and only their declarations outlive the
// bicommand — `@[scope(...)]` is what exports them. A `bi_embed` side's stay
// local to that side.
category Bicommand;

// WhyRel's `Var x:T | y:T in CC` without the `in CC`; either side may be
// omitted; nothing is initialized. For sides whose names *differ*. A shared
// name is `|- var x : T; -|` instead. Why the split is forced: docs/design.md.
@[scope(r)]
op bi_var (l : DeclList, @[scope(l)] r : DeclList) : Bicommand => "Var " l " | " r " ;";
@[scope(l)]
op bi_var_left (l : DeclList) : Bicommand => "Var " l " | ;";
@[scope(r)]
op bi_var_right (r : DeclList) : Bicommand => "Var | " r " ;";

// One statement, as WhyRel's `LEFT_SYNC atomic_command RIGHT_SYNC`. Declares
// the pair `x`/`x'` from one source name.
@[scope(c)]
op bi_sync (c : Statement) : Bicommand => "|- " c " -| ;";
op bi_embed (left : NewlineSepBy Statement, right : NewlineSepBy Statement) : Bicommand =>
  "<<\n  " indent(2, left) "\n|\n  " indent(2, right) "\n>> ;";
// WhyRel's `If e|e' then CC else DD end`. The guards are Core expressions in
// the two states; each branch is a bicommand sequence. Neither branch exports
// its declarations — a Core `if` body is a block, so they are scoped to it, as
// a split's are. Both branches see the incoming context, not each other's:
// an argument gets the previous one's context only under `@[scope(...)]`.
op bi_if (lg : bool, rg : bool, thn : Seq Bicommand, els : Seq Bicommand) : Bicommand =>
  "If " lg " | " rg " then\n  " indent(2, thn) "\nelse\n  " indent(2, els) "\nend ;";
// WhyRel's else-less form, which its parser desugars to an else of `Bisync Skip`.
op bi_if_then (lg : bool, rg : bool, thn : Seq Bicommand) : Bicommand =>
  "If " lg " | " rg " then\n  " indent(2, thn) "\nend ;";

// WhyRel's four-way `If4`, for guards that need not agree: no agreement
// obligation, a branch per combination instead.
op bi_if4 (lg : bool, rg : bool, tt : Seq Bicommand, te : Seq Bicommand,
           et : Seq Bicommand, ee : Seq Bicommand) : Bicommand =>
  "If4 " lg " | " rg
  "\nthenThen\n  " indent(2, tt)
  "\nthenElse\n  " indent(2, te)
  "\nelseThen\n  " indent(2, et)
  "\nelseElse\n  " indent(2, ee) "\nend ;";

// Loop invariants, as WhyRel's `biwhile_spec` minus `effects` (needs regions)
// and `variant` (a bi-expression, and Core's measure is one expression).
// Declared before the body and unannotated, so they see the scope the loop
// starts in, not the body's own declarations.
category BiInvariant;
op bi_invariant (r : RFormula) : BiInvariant => "\n  invariant { " r " }";

// WhyRel's `While e|e' . p|p' do ... done`. `p`/`p'` are the alignment guards:
// when `p` holds the left may step alone, when `p'` holds the right may. Both
// false is lockstep. docs/design.md has the lowering and where it comes from.
op bi_while (lg : bool, rg : bool, la : RFormula, ra : RFormula,
             invs : Seq BiInvariant, body : Seq Bicommand) : Bicommand =>
  "While " lg " | " rg " . " la " | " ra " do" invs "\n  " indent(2, body) "\ndone ;";

// WhyRel spells these as `Biwhile` with one guard false and the opposite
// alignment guard true; they are separate ops here because DDM has no way to
// write that desugaring in the grammar.
// WhyRel writes lockstep as a `Biwhile` whose alignment guards are both false;
// spelling it as its own op keeps the guards optional, as WhyRel's parser does.
op bi_while_lockstep (lg : bool, rg : bool, invs : Seq BiInvariant,
                      body : Seq Bicommand) : Bicommand =>
  "While " lg " | " rg " do" invs "\n  " indent(2, body) "\ndone ;";

op bi_while_left (g : bool, invs : Seq BiInvariant, body : Seq Bicommand) : Bicommand =>
  "WhileL " g " do" invs "\n  " indent(2, body) "\ndone ;";
op bi_while_right (g : bool, invs : Seq BiInvariant, body : Seq Bicommand) : Bicommand =>
  "WhileR " g " do" invs "\n  " indent(2, body) "\ndone ;";

op bi_assert (r : RFormula) : Bicommand => "Assert { " r " } ;";
op bi_assume (r : RFormula) : Bicommand => "Assume { " r " } ;";

// ---- Specs ------------------------------------------------------------
// Above the body, Boogie-style, either repeatable. `requires` carries no
// `@[scope(...)]`, so it sees only top-level declarations; `ensures` carries
// `@[scope(body)]` and sees bi-locals. That asymmetry is the point of the
// split — docs/design.md.
category RelRequires;
op rel_requires (r : RFormula) : RelRequires => "\n  requires { " r " }";

category RelEnsures;
op rel_ensures (r : RFormula) : RelEnsures => "\n  ensures { " r " }";

// Bicommand is deliberately NOT a `Command` — docs/design.md.
// `ens` is declared after `body` so `@[scope(body)]` can refer back to it; DDM
// elaborates arguments in declaration order, not syntax order. No trailing
// ";": every bicommand already ends with one.
op biproc (name : Ident, reqs : Seq RelRequires, body : Seq Bicommand,
           @[scope(body)] ens : Seq RelEnsures) : Command =>
  "biproc " name reqs ens " =\n  " indent(2, body);

#end

end Strata
end
