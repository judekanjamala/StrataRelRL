/-
  Copyright StrataRelRL Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module

public import RelRL.Cli.Common

public section

namespace Strata.RelRL.Cli

/-! # `relrl toCore`

Translate and print Core concrete syntax, so translation and verification stay
decoupled — the output is a normal `.core.st` file for any generic Core tool.
Mirrors how `laurelToCore` splits Laurel. `docs/workflows/toCore.md`. -/

def to_core_command : Command where
  name := "toCore"
  args := [ "file" ]
  flags := [includeFlag]
  help := "Translate an RelRL bicommand source file to Core and print it to stdout. \
    Save the output as a `.core.st` file to verify it with `strata verify`."
  callback := fun v pflags => do
    let fm ← build_relrl_dialect_file_map pflags
    let (pgm, ictx) ← read_relrl_program fm v[0]
    let (coreProgram, diagnostics) :=
      Strata.RelRL.TranslateM.run (Strata.RelRL.translate_program pgm ictx)
    report_diagnostics ictx diagnostics
    IO.println (StrataDDM.Program.toString (Strata.coreToStrataProgram coreProgram))
    -- Printing is the point, so the output still goes out — but a fatal
    -- diagnostic means it is not the program written, and exiting 0 would hand
    -- a silently-wrong Core file to whatever consumes it next.
    if diagnostics.any (fun d => d.kind.impact.isFatal) then
      IO.Process.exit (diagnostics_exit_code diagnostics)

end Strata.RelRL.Cli
