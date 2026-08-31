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
// Bicommand is deliberately NOT a `Command` — docs/design.md.

category Bicommand;

@[scope(r)]
op bi_var (l : DeclList, @[scope(l)] r : DeclList) : Bicommand => "Var " l " | " r " ;";
@[scope(l)]
op bi_var_left (l : DeclList) : Bicommand => "Var " l " | ;";
@[scope(r)]
op bi_var_right (r : DeclList) : Bicommand => "Var | " r " ;";

@[scope(c)]
op bi_sync (c : Statement) : Bicommand => "|- " c " -| ;";
@[scope(right)]
op bi_embed (left : NewlineSepBy Statement,
             @[scope(left)] right : NewlineSepBy Statement) : Bicommand =>
  "<<\n  " indent(2, left) "\n|\n  " indent(2, right) "\n>> ;";

op bi_if (lg : bool, rg : bool, thn : Seq Bicommand, els : Seq Bicommand) : Bicommand =>
  "If " lg " | " rg " then\n  " indent(2, thn) "\nelse\n  " indent(2, els) "\nend ;";

// WhyRel's else-less form, which its parser desugars to an else of Bisync
// Skip. They are separate ops here because DDM has no way to
// write that desugaring in the grammar.
op bi_if_then (lg : bool, rg : bool, thn : Seq Bicommand) : Bicommand =>
  "If " lg " | " rg " then\n  " indent(2, thn) "\nend ;";

op bi_if4 (lg : bool, rg : bool, tt : Seq Bicommand, te : Seq Bicommand,
           et : Seq Bicommand, ee : Seq Bicommand) : Bicommand =>
  "If4 " lg " | " rg
  "\nthenThen\n  " indent(2, tt)
  "\nthenElse\n  " indent(2, te)
  "\nelseThen\n  " indent(2, et)
  "\nelseElse\n  " indent(2, ee) "\nend ;";

category BiInvariant;
op bi_invariant (r : RFormula) : BiInvariant => "\n  invariant { " r " }";

// docs/design.md has the lowering and where it comes from.
op bi_while (lg : bool, rg : bool, la : RFormula, ra : RFormula,
             invs : Seq BiInvariant, body : Seq Bicommand) : Bicommand =>
  "While " lg " | " rg " . " la " | " ra " do" invs "\n  " indent(2, body) "\ndone ;";

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
category RelRequires;
op rel_requires (r : RFormula) : RelRequires => "\n  requires { " r " }";

category RelEnsures;
op rel_ensures (r : RFormula) : RelEnsures => "\n  ensures { " r " }";

// Each side's parameters are a Core `Bindings`, so `out`/`inout` and
// `translateProcBindings` come for free. That is why the parens are per side
// rather than around the pair as WhyRel writes them — docs/status.md records
// the spelling difference.
category BiBindings;
@[scope(r)]
op bi_bindings (l : Bindings, @[scope(l)] r : Bindings) : BiBindings => l " |" r;

// Both clauses are scoped to the parameters: a spec names what the caller can
// see, never what the body declares. They become Core's own pre/postconditions,
// which is what makes `old x` mean the entry value — docs/design.md.
op biproc (name : Ident, params : Option BiBindings,
           @[scope(params)] reqs : Seq RelRequires,
           @[scope(params)] ens : Seq RelEnsures,
           @[scope(params)] body : Seq Bicommand) : Command =>
  "biproc " name params reqs ens " =\n  " indent(2, body);

#end

end Strata
end
