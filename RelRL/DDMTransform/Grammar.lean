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

-- ` The grammar is a build product, not a file read
-- at run time — an ill-formed rule is a compile error pointing here, `relrl`
-- never opens this file, and a `#strata … #end` block elsewhere tests the same
-- compiled `Dialect`. `Cli/Common.lean` hands the constant to the parser.
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

// Sugar for `x =:= x`; `Desugar.lean` rewrites it, so lowering has no case.
op rf_agree (tp : Type, x : tp) : RFormula => "Agree " x;
op rf_both (p : bool) : RFormula => "Both" " (" p ")";
op rf_left (p : bool) : RFormula => "<| " p " <]";
op rf_right (p : bool) : RFormula => "[> " p " |>";
op rf_biequal (tp : Type, l : tp, r : tp) : RFormula => @[prec(15)] l " =:= " r;
op rf_group (r : RFormula) : RFormula => "{ " r " }";
op rf_not (r : RFormula) : RFormula => @[prec(20)] "~ " r;
op rf_and (l : RFormula, r : RFormula) : RFormula => @[prec(10), leftassoc] l " /\\ " r;
op rf_or (l : RFormula, r : RFormula) : RFormula => @[prec(8), leftassoc] l " \\/ " r;
op rf_implies (l : RFormula, r : RFormula) : RFormula => @[prec(5), rightassoc] l " => " r;
op rf_iff (l : RFormula, r : RFormula) : RFormula => @[prec(4)] l " <=> " r;

// WhyRel's `Rlet`: name a value from either program, then say what you like
// about the names. `[< e <]` reads the left state and `[> e >]` the right, and
// the body is an ordinary relational formula — so this one form is how *all* of
// Core's expression language reaches across the two programs. docs/design.md.
category BiLetBind;
@[declare(x, tp)]
op bilet_left (tp : Type, x : Ident, e : tp) : BiLetBind => x " = [< " e " <]";
@[declare(x, tp)]
op bilet_right (tp : Type, x : Ident, e : tp) : BiLetBind => x " = [> " e " >]";

category BiLetBinds;
@[scope(b)]
op biletAtom (b : BiLetBind) : BiLetBinds => b;
@[scope(b)]
op biletPush (bs : BiLetBinds, @[scope(bs)] b : BiLetBind) : BiLetBinds =>
  bs:0 ", " b:0;

op rf_let (bs : BiLetBinds, @[scope(bs)] b : RFormula) : RFormula =>
  @[prec(3)] "Let " bs " :: " b;

// WhyRel's `Rquant`: a binder list per side, either side omittable, or one
// list both readings share. Nothing here is program state, so nothing is
// primed — and that is why `l | r` needs the two sides' names to differ.
category BiQuantBindings;
@[scope(r)]
op biq_both (l : DeclList, @[scope(l)] r : DeclList) : BiQuantBindings => l " | " r;
@[scope(l)]
op biq_left (l : DeclList) : BiQuantBindings => l " |";
@[scope(r)]
op biq_right (r : DeclList) : BiQuantBindings => "| " r;
@[scope(x)]
op biq_shared (x : DeclList) : BiQuantBindings => x;

// `::` rather than WhyRel's `.`: after a type, a `.` is read as the start of a
// qualified name (`int.add`), so `int . R` fails with `expected identifier`.
// It is also what Core's own `forall d :: b` uses — docs/status.md.
op rf_forall (xs : BiQuantBindings, @[scope(xs)] b : RFormula) : RFormula =>
  @[prec(3)] "Forall " xs " :: " b;
op rf_exists (xs : BiQuantBindings, @[scope(xs)] b : RFormula) : RFormula =>
  @[prec(3)] "Exists " xs " :: " b;

// ---- Bicommands -------------------------------------------------------
// Bicommand is deliberately NOT a `Command` — docs/design.md.

category Bicommand;

@[scope(r)]
op bi_var (l : DeclList, @[scope(l)] r : DeclList) : Bicommand => "Var " l " | " r " ;";
@[scope(l)]
op bi_var_left (l : DeclList) : Bicommand => "Var " l " |" " ;";
@[scope(r)]
op bi_var_right (r : DeclList) : Bicommand => "Var" " | " r " ;";

op bi_sync (c : Statement) : Bicommand => "|- " c " -|" " ;";

// obligation. `Call` rather than Core's `call` because the callee is a biproc
// and matches with rest of the Bicom style; docs/design.md.
op bi_call (name : Ident, largs : CommaSepBy CallArg,
            rargs : CommaSepBy CallArg) : Bicommand =>
  "|- " "Call " name " (" largs ")" " |" " (" rargs ")" " -|" " ;";
op bi_embed (left : NewlineSepBy Statement,
             right : NewlineSepBy Statement) : Bicommand =>
  "<<\n  " indent(2, left) "\n|\n  " indent(2, right) "\n>>" " ;";

op bi_if (lg : bool, rg : bool, thn : Seq Bicommand, els : Seq Bicommand) : Bicommand =>
  "If " lg " | " rg " then\n  " indent(2, thn) "\nelse\n  " indent(2, els) "\nend" " ;";

// WhyRel's else-less form, which its parser desugars to an else of Bisync
// Skip. They are separate ops here because DDM has no way to
// write that desugaring in the grammar.
op bi_if_then (lg : bool, rg : bool, thn : Seq Bicommand) : Bicommand =>
  "If " lg " | " rg " then\n  " indent(2, thn) "\nend" " ;";

op bi_if4 (lg : bool, rg : bool, tt : Seq Bicommand, te : Seq Bicommand,
           et : Seq Bicommand, ee : Seq Bicommand) : Bicommand =>
  "If4 " lg " | " rg
  "\nthenThen\n  " indent(2, tt)
  "\nthenElse\n  " indent(2, te)
  "\nelseThen\n  " indent(2, et)
  "\nelseElse\n  " indent(2, ee) "\nend" " ;";

category BiInvariant;
op bi_invariant (r : RFormula) : BiInvariant => "\n  invariant" " { " r " }";

op bi_while (lg : bool, rg : bool, la : RFormula, ra : RFormula,
             invs : Seq BiInvariant, body : Seq Bicommand) : Bicommand =>
  "While " lg " | " rg " . " la " | " ra " do" invs "\n  " indent(2, body) "\ndone" " ;";

op bi_while_lockstep (lg : bool, rg : bool, invs : Seq BiInvariant,
                      body : Seq Bicommand) : Bicommand =>
  "While " lg " | " rg " do" invs "\n  " indent(2, body) "\ndone" " ;";

op bi_while_left (g : bool, invs : Seq BiInvariant, body : Seq Bicommand) : Bicommand =>
  "WhileL " g " do" invs "\n  " indent(2, body) "\ndone" " ;";
op bi_while_right (g : bool, invs : Seq BiInvariant, body : Seq Bicommand) : Bicommand =>
  "WhileR " g " do" invs "\n  " indent(2, body) "\ndone" " ;";

op bi_assert (r : RFormula) : Bicommand => "Assert" " { " r " }" " ;";
op bi_assume (r : RFormula) : Bicommand => "Assume" " { " r " }" " ;";

// ---- Specs ------------------------------------------------------------
category RelRequires;
op rel_requires (r : RFormula) : RelRequires => "\n  requires" " { " r " }";

category RelEnsures;
op rel_ensures (r : RFormula) : RelEnsures => "\n  ensures" " { " r " }";

// Each side's parameters are a Core `Bindings`, so `out`/`inout` and
// `translateProcBindings` come for free. That is why the parens are per side
// rather than around the pair as WhyRel writes them — docs/status.md records
// the spelling difference.
category BiBindings;
@[scope(r)]
op bi_bindings (l : Bindings, @[scope(l)] r : Bindings) : BiBindings => l " |" r;

// Requires and ensures become Core's own pre/postconditions,
// which is what makes `old x` mean the entry value — docs/design.md.
op biproc (name : Ident, params : Option BiBindings,
           @[scope(params)] reqs : Seq RelRequires,
           @[scope(params)] ens : Seq RelEnsures,
           @[scope(params)] body : Seq Bicommand) : Command =>
  "biproc " name params reqs ens " =\n  " indent(2, body);

#end

end Strata
end
