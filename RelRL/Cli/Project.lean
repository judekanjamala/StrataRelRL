/-
  Copyright StrataRelRL Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module

public import RelRL.Cli.Common

public section

namespace Strata.RelRL.Cli

/-! # `relrl project`

```console
relrl project <file.relrl.st> --side left|right [--include <dir>]...
```

Print one side of every `biproc` as an ordinary unary Core program — one
procedure per `biproc`, under its own name. A relational judgement is a statement
about two programs; `verify` checks it by fusing them, and `project` recovers the
two being talked about. It answers "what exactly is the left-hand program here?",
which is what you want when a spec fails and the question is whether the fault is
in one side or in the relation between them.

`Mode` in `Translate/State.lean` says what a projection drops and why. The short
version: the other side, all priming, and every relational formula. Contrast
`toCore` on the same file — there the block is labelled `biproc` and holds both
sides with the right one primed; here it is labelled with the side, and names are
unprimed in *both* projections.

## Exit codes

| Code | Meaning | Trigger |
|---|---|---|
| 0 | printed | |
| 1 | user error | missing or unrecognised `--side`, parse error, unreadable file, or an error in the source program |
| 3 | `internalError` | a broken translator invariant — the program printed is not the program written |

One source error reaches projection: a `datatype`, or a `rec` block of more than
one function, in a file that also declares a `biproc`. That guard is deliberately
not mode-gated — the top-level binding list every body is lowered against is as
wrong here as under `verify` (`docs/issues.md`). No body is lowered once it
fires, so what prints is the Core declarations alone.

The duplicate-declaration check does *not* run here: it is about names colliding
in the one block self-composition fuses, and a projection has no such block. The
exit-3 row is defensive — the remaining diagnostics come from
`emit_invariant_violation`, which fires only if grammar and translator have
drifted. A relational formula Core would reject does not reach it either, since
projection drops formulas before lowering them; `project` exits 0 on a file
`verify` exits 3 on.

`--side` is required and accepts exactly `left` or `right` (`Side.of_string?`). -/

def side_flag : Flag :=
  { name := "side", help := "Which side of each biproc to keep: left or right.",
    takesArg := .arg "left|right" }

def project_command : Command where
  name := "project"
  args := [ "file" ]
  flags := [side_flag, includeFlag]
  help := "Project an RelRL bicommand source file onto one side and print the resulting \
    Core program to stdout. Each `biproc` becomes a Core procedure of the same name \
    holding that side alone, keeping its source names — the right side is not primed, \
    since nothing else shares its scope. A relational `ensures` names both sides, so it \
    is dropped. Save the output as a `.core.st` file to verify one side on its own with \
    `strata verify`."
  callback := fun v pflags => do
    let some sideName := pflags.getString "side"
      | exitFailure "project requires --side left or --side right." "relrl project --help"
    let some side := Strata.RelRL.Side.of_string? sideName
      | exitFailure s!"Unknown side '{sideName}': expected left or right."
          "relrl project --help"
    let fm ← build_relrl_dialect_file_map pflags
    let (pgm, ictx) ← read_relrl_program fm v[0]
    let (coreProgram, diagnostics) :=
      Strata.RelRL.TranslateM.run (Strata.RelRL.project_program side pgm ictx)
    report_diagnostics ictx diagnostics
    IO.println (StrataDDM.Program.toString (Strata.coreToStrataProgram coreProgram))
    -- A diagnostic means the program printed is not the program written.
    if !diagnostics.isEmpty then
      IO.Process.exit (diagnostics_exit_code diagnostics)

end Strata.RelRL.Cli
