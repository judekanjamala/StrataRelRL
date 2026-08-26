/-
  Copyright StrataRelRL Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module

import Lean.Parser.Extension

public import RelRL.Verify
public import Strata.Cli.Framework
public import Strata.Cli.VerifyOptions
public import StrataDDM.Util.IO
public import StrataDDM.BuiltinDialects

public section

namespace Strata.RelRL.Cli

/-! # RelRL CLI command definitions

Both commands reuse `Strata.Cli.Framework`, as the built-in `Core`/`Laurel`
commands do.

- `verify <file>`: parse, translate and verify in one step, one pass/fail line
  per obligation.
- `toCore <file>`: translate and print Core concrete syntax, so translation and
  verification stay decoupled — the output is a normal `.core.st` file for any
  generic Core tool. Mirrors how `laurelToCore` splits Laurel. -/

/-- Preload `Core` and `RelRL` (plus DDM builtins) so `.relrl.st` files parse
without an `--include` search path. -/
def build_relrl_dialect_file_map (pflags : ParsedFlags) : IO StrataDDM.DialectFileMap := do
  let preloaded := StrataDDM.Elab.LoadedDialects.builtin
    |>.addDialect! Strata.Core
    |>.addDialect! Strata.RelRL
  let mut fm ← StrataDDM.DialectFileMap.new preloaded
  for path in pflags.getRepeated "include" do
    match ← fm.add path |>.toBaseIO with
    | .error msg => exitFailure msg
    | .ok fm' => fm := fm'
  return fm

/-- Read and parse a program file via the DDM API, as the `strata` binary's
`readStrataProgram` does for any dialect. -/
def read_relrl_program (fm : StrataDDM.DialectFileMap) (file : String) :
    IO (StrataDDM.Program × Lean.Parser.InputContext) := do
  let text ← StrataDDM.Util.readInputSource file
  let displayPath := StrataDDM.Util.displayName file
  let inputCtx := Lean.Parser.mkInputContext text displayPath
  match ← StrataDDM.readStrataText fm displayPath text.toUTF8 with
  | .program pgm => pure (pgm, inputCtx)
  | .dialect _ => throw (IO.userError s!"Expected an RelRL program file, got a dialect: {file}")

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
    for d in diagnostics do
      IO.eprintln s!"{Message.format d (some ictx.fileMap)}"
    IO.println (StrataDDM.Program.toString (Strata.coreToStrataProgram coreProgram))

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
    for d in diagnostics do
      IO.eprintln s!"{Message.format d (some ictx.fileMap)}"
    for vcResult in vcResults do
      let posStr := Imperative.MetaData.formatFileRangeD vcResult.obligation.metadata (some ictx.fileMap)
      println! f!"{posStr} [{vcResult.obligation.label}]: {vcResult.formatOutcome}"
    -- A diagnostic means the program verified is not the program written, so
    -- it fails the run even when every obligation discharged.
    if !diagnostics.isEmpty then
      println! f!"Finished with {vcResults.size} goals checked, \
        but {diagnostics.size} translation error(s) occurred."
      IO.Process.exit ExitCode.internalError
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
