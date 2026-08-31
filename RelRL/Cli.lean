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
  generic Core tool. Mirrors how `laurelToCore` splits Laurel.
- `project <file> --side left|right`: print the Core concrete syntax of one side
  of every `biproc` — the unary program that side denotes, with neither the
  other side nor the relational `ensures`. -/

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

/-- What a run of diagnostics should exit with. An error in the user's program
exits 1; anything else a diagnostic reports is a translator bug, which exits 3
so it is not mistaken for a rejected program. -/
def diagnostics_exit_code (ds : Array Message) : UInt8 :=
  if ds.any (fun d => d.kind.impact != .userCodeError) then ExitCode.internalError
  else ExitCode.userError

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
    -- Printing is the point, so the output still goes out — but a fatal
    -- diagnostic means it is not the program written, and exiting 0 would hand
    -- a silently-wrong Core file to whatever consumes it next.
    if diagnostics.any (fun d => d.kind.impact.isFatal) then
      IO.Process.exit (diagnostics_exit_code diagnostics)

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
    for d in diagnostics do
      IO.eprintln s!"{Message.format d (some ictx.fileMap)}"
    IO.println (StrataDDM.Program.toString (Strata.coreToStrataProgram coreProgram))
    -- A diagnostic means the program printed is not the program written.
    if !diagnostics.isEmpty then
      IO.Process.exit (diagnostics_exit_code diagnostics)

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
