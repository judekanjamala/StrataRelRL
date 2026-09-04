/-
  Copyright StrataRelRL Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module

public import RelRL.Cli.Common
public import Strata.Cli.VerifyOptions

public section

namespace Strata.RelRL.Cli

/-! # `relrl verify`

```console
relrl verify <file.relrl.st> [--include <dir>]... [verify options]
```

Parse, translate and discharge every proof obligation: one line per
obligation, then a summary.

Flags are `--include` plus Core's own `verifyOptionsFlags` — solver selection,
timeouts, VC dump directory, verbosity; verbosity is forced to `.quiet` so the
per-obligation lines are the whole output.

## Exit codes

| Code | Meaning | Trigger |
|---|---|---|
| 0 | all obligations discharged | |
| 1 | user error | parse error, or an error in the source program |
| 2 | `failuresFound` | a spec that does not hold |
| 3 | `internalError` | a solver or translator failure |

`_root_.Core.VerifyOptions` is spelled out because `Strata.Core` (the dialect
value) shadows the `Core` namespace here — CLAUDE.md, "Two `Core` namespaces". -/

def verify_command : Command where
  name := "verify"
  args := [ "file" ]
  flags := includeFlag :: verifyOptionsFlags
  help := "Translate and verify an RelRL bicommand source file (.relrl.st) directly, \
    without a separate toCore + verify step."
  callback := fun v pflags => do
    let file := v[0]
    let opts ← parseVerifyOptions pflags { _root_.Core.VerifyOptions.default with verbose := .quiet }
      (inputFile := some file)
    let fm ← build_relrl_dialect_file_map pflags
    let (pgm, ictx) ← read_relrl_program fm file
    let (vcResults, diagnostics) ← try
      Strata.RelRL.verify pgm ictx opts
    catch e =>
      println! f!"{e}"
      IO.Process.exit ExitCode.internalError
    report_diagnostics ictx diagnostics
    for vcResult in vcResults do
      let posStr := Imperative.MetaData.formatFileRangeD vcResult.obligation.metadata (some ictx.fileMap)
      println! f!"{posStr} [{vcResult.obligation.label}]: {vcResult.formatOutcome}"
    -- A diagnostic means the program verified is not the program written, so
    -- it fails the run even when every obligation discharged.
    if !diagnostics.isEmpty then
      println! f!"Finished with {vcResults.size} goals checked, \
        but {diagnostics.size} error(s) occurred."
      IO.Process.exit (diagnostics_exit_code diagnostics)
    let success := vcResults.all _root_.Core.VCResult.isSuccess
    if success then
      println! f!"All {vcResults.size} goals passed."
    else
      let provedGoalCount := (vcResults.filter _root_.Core.VCResult.isSuccess).size
      let failedGoalCount := (vcResults.filter _root_.Core.VCResult.isNotSuccess).size
      let hasImplError := vcResults.any (fun r => r.isImplementationError || r.hasSMTError)
      let hasFailure := vcResults.any
        (fun r => !r.isSuccess && !r.isTimeout && !r.isImplementationError && !r.hasSMTError)
      println! f!"Finished with {provedGoalCount} goals passed, {failedGoalCount} failed."
      if hasImplError then
        IO.Process.exit ExitCode.internalError
      else if hasFailure then
        IO.Process.exit ExitCode.failuresFound

end Strata.RelRL.Cli
