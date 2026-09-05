/-
  Copyright StrataRelRL Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module

public import RelRL.DDMTransform.Grammar
import StrataDDM.AST

namespace Strata
namespace RelRL

public section

open StrataDDM (Arg)

/-! # Desugaring, between parsing and lowering

One rewrite per surface form that is defined as another, so `Bicommands.lean`
lowers a smaller language than the grammar accepts. Runs once, at the top of
`translate_program_with`, so `verify`, `toCore`, `project` and `bi_while`'s own
re-lowering of its body all see the same tree.

**A rewrite here must not change binder depth.** `read_relrl_program` returns an
*elaborated* program: an expression inside it is already `ExprF.bvar i` against
the `@[scope(…)]` chain, and `ExprF.fvar i` against the top-level declarations.
Moving, copying or re-parenting a subterm under a different number of enclosing
binders silently rebinds every index in it — and there is no `ExprF.incIndices`
to repair it with, only the one for types. So: no rewrite may introduce a
binder, drop one, reorder two, or lift a subterm out of one. A fresh temporary
is therefore out of reach from here; that needs the lowering, which builds Core
terms rather than rewriting DDM ones.

Two further rules keep this honest. A synthesized node reuses the original's
`ann`, so a diagnostic still points at what the user wrote. And only
`RelRL.biproc` commands are rewritten — a Core command must reach
`translateCoreDecls` byte-identical, since `translate_program_with` rebuilds the
top-level binding list by position. -/

/-- Rewrite one argument, bottom-up so a form nested inside another is already
desugared when its parent is rewritten. Every argument is walked, not only the
bicommand ones: a Core subtree simply holds no `RelRL` operator to match. -/
partial def desugar_arg (a : Arg) : Arg :=
  match a with
  | .op op =>
    let op := { op with args := op.args.map desugar_arg }
    match op.name, op.args with
    -- WhyRel's else-less `If`, which its own parser desugars to an else of
    -- `Bisync Skip`. An empty sequence is that, and adds no binder.
    | q`RelRL.bi_if_then, #[lg, rg, thn] =>
      .op { ann := op.ann, name := q`RelRL.bi_if,
            args := #[lg, rg, thn, .seq op.ann .newline #[]] }
    -- `Agree x` is `x =:= x` by definition: one expression, read in each
    -- state. The operand is copied into two positions at the same depth,
    -- neither of which binds.
    | q`RelRL.rf_agree, #[tp, e] =>
      .op { ann := op.ann, name := q`RelRL.rf_biequal, args := #[tp, e, e] }
    -- `Both (e)` is `<| e <] /\ [> e |>` by definition, and writing it that way
    -- puts it in reach of `top_conjuncts`: one obligation per side, so a failure
    -- names the program it happened in. The `bool` is duplicated into two
    -- positions at the same depth, neither of which binds.
    | q`RelRL.rf_both, #[e] =>
      .op { ann := op.ann, name := q`RelRL.rf_and,
            args := #[.op { ann := op.ann, name := q`RelRL.rf_left, args := #[e] },
                      .op { ann := op.ann, name := q`RelRL.rf_right, args := #[e] }] }
    | _, _ => .op op
  | .seq ann sep as => .seq ann sep (as.map desugar_arg)
  | .option ann (some b) => .option ann (some (desugar_arg b))
  | _ => a

/-- Desugar every `biproc`, leaving Core commands untouched. -/
def desugar_program (p : StrataDDM.Program) : StrataDDM.Program :=
  { p with commands := p.commands.map fun op =>
      if op.name == q`RelRL.biproc then { op with args := op.args.map desugar_arg } else op }

end
end RelRL
end Strata
