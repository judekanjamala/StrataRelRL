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

Parse, translate and discharge every proof obligation in one step: one line per
obligation, then a summary. Needs an SMT solver on `PATH` (cvc5 by default).
Flags are `--include` plus Core's own `verifyOptionsFlags` — solver selection,
timeouts, VC dump directory, verbosity; verbosity is forced to `.quiet` so the
per-obligation lines are the whole output.

Because the last stage is Core's unmodified verifier, every obligation reported
is an ordinary Core assertion. What makes it *relational* is entirely what the
translation built.

## Exit codes

| Code | Meaning | Trigger |
|---|---|---|
| 0 | all obligations discharged | |
| 1 | user error | parse error, or an error in the source program |
| 2 | `failuresFound` | a spec that does not hold |
| 3 | `internalError` | a solver or translator failure |

## Failure modes

- **A spec that does not hold** — reported per obligation, exit 2. Each line is
  one conjunct, at the source position of the clause it came from.
- **A name a spec got wrong** — exit 1. `Agree x` takes an `Ident`, so DDM never
  elaborates it; `check_formula` checks the operand and says which program is
  missing it. Every other relational form is a Core expression, so DDM catches a
  bad name there first, at the same position.
- **A name declared twice** — exit 1, against the declaration. Both programs land
  in one Core scope, so a name must be unique there under its Core name, which
  for the right program carries the prime. Verification is skipped, since the
  Core program would not be the one the source denotes. Note what is *not* an
  error: `Var n : int | n : int ;` declares `n` and `n'`, one per program.
- **A `datatype` or multi-function `rec` block beside a `biproc`** — refused
  against the offending command, exit 1. `docs/issues.md` has the mechanism.
- **A synchronized `Call` that no `biproc` answers, or whose argument list does
  not match one side's parameters** — exit 1, against the call. The arity is
  checked per side here because Core checks it only after the two sides have
  been fused into one list. A `Call` inside a `While` with alignment guards is
  refused the same way; `docs/design.md` says why it has no meaning there.
- **A parse error** — reported against the source with a line and column, exit 1.

## Debugging a failure

`verify` gives the verdict, not the program that was checked. When an obligation
fails and the reason is not obvious, run `toCore` on the same file to see the
self-composed program the solver saw, and `project` to check each side alone.

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
