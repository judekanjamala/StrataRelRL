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

`--side` is required and accepts exactly `left` or `right` (`Side.of_string?`).

Print either side of every `biproc` as an ordinary unary Core program — one
procedure per `biproc`, under its own name.


## Exit codes

| Code | Meaning | Trigger |
|---|---|---|
| 0 | printed | |
| 1 | user error | missing or unrecognised `--side`, parse error, unreadable file, or an error in the source program |
| 3 | `internalError` | a broken translator invariant — the program printed is not the program written |

The exit-3 row is defensive — the remaining diagnostics come from
`emit_invariant_violation`, which fires only if grammar and translator have
drifted. A relational formula Core would reject does not reach it either, since
projection drops formulas before lowering them; `project` exits 0 on a file
`verify` exits 3 on.

-/

def side_flag : Flag :=
  { name := "side", help := "Which side of each biproc to keep: left or right.",
    takesArg := .arg "left|right" }

def project_command : Command where
  name := "project"
  args := [ "file" ]
  flags := [side_flag, includeFlag]
  help := "Project an RelRL bicommand source file onto one side and print the resulting \
    Core program to stdout. Each `biproc` becomes a Core procedure of the same name \
    holding that side alone, keeping its source names — the right side is not primed."
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
