/-
  Copyright StrataRelRL Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module

public import RelRL.DDMTransform.Translate.Diagnostics
public import RelRL.DDMTransform.Translate.Priming
public import RelRL.DDMTransform.Translate.Formulas
public import RelRL.DDMTransform.Translate.State
public import RelRL.DDMTransform.Translate.Bicommands
public import RelRL.DDMTransform.Translate.Program

/-! # RelRL to Core translation

A `biproc` becomes a Core procedure holding both programs at once: the left side
keeps its source names, every right-side name is primed, and a relational formula
is then an ordinary Core `assert` over both. The prime is what separates the two
programs in the one Core scope they now share, so it holds for asymmetric names
too — `Var | u : int ;` declares the right program's `u`, which is `u'` in Core.

The two are interleaved per bicommand: `(l₁|r₁); (l₂|r₂)` becomes
`l₁; r₁; l₂; r₂`, following WhyRel, where `Bisplit` emits its left then its
right and `Biseq` composes those. CLAUDE.md says what breaks if that order is
changed.

Lowering runs inside Core's `TransM`, threading its `TransBindings` from one
side to the next. **That threading mirrors the `@[scope(…)]` chain in
`Grammar.lean` and must be kept in step with it** — see CLAUDE.md, "The other
invariant". `docs/workflows/pipeline.md` walks the stages; `docs/design.md`
argues the choices.

This module is the aggregator. One submodule per stage, in dependency order:
`Diagnostics`, `Priming`, `Formulas`, `State`, `Bicommands`, `Program`. -/
