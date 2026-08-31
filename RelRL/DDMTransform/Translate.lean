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

This module is the aggregator. One submodule per stage, in dependency order:
`Diagnostics`, `Priming`, `Formulas`, `State`, `Bicommands`, `Program`. -/
