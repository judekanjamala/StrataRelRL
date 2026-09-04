/-
  Copyright StrataRelRL Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module

public import RelRL.DDMTransform.Translate.Diagnostics
public import RelRL.DDMTransform.Translate.Priming
public import RelRL.DDMTransform.Translate.Formulas
public import RelRL.DDMTransform.Translate.State
public import RelRL.DDMTransform.Translate.Sides
public import RelRL.DDMTransform.Translate.Projection
public import RelRL.DDMTransform.Translate.Composition
public import RelRL.DDMTransform.Translate.Program

/-! # RelRL to Core translation

There are two types of translation: toCore and project. Both start from a parsed `StrataDDM.Program` and end in a `Core.Program`, and
both run `translate_program_with`.

| Entry point | Mode | Produces | Drives |
|---|---|---|---|
| `translate_program` | `.compose` | both programs in one procedure, the right one primed
| `project_program side` | `.project side` | that side alone, unprimed, with every relational formula dropped — specs, `Assert`/`Assume`, loop invariants

`.project` is not only a printing aid: `bi_while` lowers its body through it to
get the steps only one side takes.

## Where to look

| Module | Does |
|---|---|
| `../Desugar` | rewrites each surface form that is defined as another, before any body is lowered |
| `Diagnostics` | collects located messages, so a bad program or a broken invariant is reported rather than aborting the run |
| `Priming` | computes the names a fragment mentions, and renames a right-hand one apart |
| `Formulas` | lowers a relational formula to one Core `bool`, and peels a top-level `/\` into separate conjuncts |
| `State` | defines `Side` and `Mode`, carries the body accumulator, emits each bicommand into it, and checks declarations and names against what each side has |
| `Sides` | lowers one side's statements, a `Var`'s declarations and a `Call`'s arguments back through Core's own translator, and checks the result |
| `Projection` | lowers a bicommand onto one side alone |
| `Composition` | lowers a bicommand into both programs at once; uses `Projection` for a `While`'s one-sided steps, never the reverse |
| `Program` | lowers specs and parameters, assembles each `biproc` into a Core procedure, and walks the top level |
-/
