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

The aggregator. Nothing is defined here; this is the map.

## The two workflows

Both start from a parsed `StrataDDM.Program` and end in a `Core.Program`, and
both run `translate_program_with` — they differ only in the `Mode` it carries,
which every bicommand form reads.

| Entry point | Mode | Produces | Drives |
|---|---|---|---|
| `translate_program` | `.verify` | both programs in one procedure, the right one primed | `verify`, `toCore` |
| `project_program side` | `.project side` | that side alone, unprimed, with every relational formula dropped — specs, `Assert`/`Assume`, loop invariants | `project` |

A `biproc` becomes a Core procedure of the same name either way; every other
top-level command is Core syntax and is handed to Core unchanged.

`.project` is not only a printing aid: `bi_while` lowers its body through it to
get the steps only one side takes.

## Where to look

| Module | Does |
|---|---|
| `Diagnostics` | collects located messages, so a bad program or a broken invariant is reported rather than aborting the run |
| `Priming` | computes the names a fragment mentions, and renames a right-hand one apart |
| `Formulas` | lowers a relational formula to one Core `bool`, and peels a top-level `/\` into separate conjuncts |
| `State` | defines `Side` and `Mode`, carries the body accumulator, emits each bicommand into it, and checks declarations and names against what each side has |
| `Bicommands` | lowers one bicommand, of any form, and folds over a nested sequence |
| `Program` | lowers specs and parameters, assembles each `biproc` into a Core procedure, and walks the top level |

`docs/workflows.md` relates the workflows; `docs/design.md` argues the
choices. -/
