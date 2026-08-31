/-
  Copyright StrataRelRL Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module

public import RelRL.Cli.Common

public section

namespace Strata.RelRL.Cli

/-! # `relrl project`

Print the Core concrete syntax of one side of every `biproc` — the unary program
that side denotes, with neither the other side nor the relational `ensures`.
`docs/workflows/project.md`. -/

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
