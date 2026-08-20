/-
  Copyright RRL Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module

import Lean.Parser.Extension

public import RRL.Verify
public import Strata.Cli.Framework
public import Strata.Cli.VerifyOptions
public import StrataDDM.Util.IO
public import StrataDDM.BuiltinDialects

public section

namespace Strata.RRL.Cli

/-! # RRL CLI command definitions

Two ways to drive verification of an RRL bicommand program from the
command line, both reusing the unified `strata` CLI's framework
(`Strata.Cli.Framework`) the same way `StrataPython.Cli` and the built-in
`Core`/`Laurel` commands do:

- `rrlVerify <file>`: parse, translate, and verify an RRL `.rrl.st` file in
  one step, printing one pass/fail line per proof obligation (mirroring the
  generic `verify` command's output and exit-code scheme).
- `rrlToCore <file>`: translate an RRL `.rrl.st` file to Core concrete
  syntax and print it to stdout. The output is a normal `.core.st` file, so
  it can be saved and verified with the *generic* `strata verify` command
  (`Core.verify`/`Core.verifyProgram`) without any RRL-specific tooling —
  i.e., RRL→Core translation and Core verification are decoupled, just like
  `laurelToCore` decouples Laurel translation from Core verification. -/

/-- Preload the `Core` and `RRL` dialects (plus DDM builtins) so that
`.rrl.st` files can be parsed without a separate `--include` search path. -/
def buildRRLDialectFileMap (pflags : ParsedFlags) : IO StrataDDM.DialectFileMap := do
  let preloaded := StrataDDM.Elab.LoadedDialects.builtin
    |>.addDialect! Strata.Core
    |>.addDialect! Strata.RRL
  let mut fm ← StrataDDM.DialectFileMap.new preloaded
  for path in pflags.getRepeated "include" do
    match ← fm.add path |>.toBaseIO with
    | .error msg => exitFailure msg
    | .ok fm' => fm := fm'
  return fm

/-- Read and parse an RRL program file via the DDM API, the same way the
unified `strata` binary's `readStrataProgram` helper reads any other
dialect's file. -/
def readRRLProgram (fm : StrataDDM.DialectFileMap) (file : String) :
    IO (StrataDDM.Program × Lean.Parser.InputContext) := do
  let text ← StrataDDM.Util.readInputSource file
  let displayPath := StrataDDM.Util.displayName file
  let inputCtx := Lean.Parser.mkInputContext text displayPath
  match ← StrataDDM.readStrataText fm displayPath text.toUTF8 with
  | .program pgm => pure (pgm, inputCtx)
  | .dialect _ => throw (IO.userError s!"Expected an RRL program file, got a dialect: {file}")

def rrlToCoreCommand : Command where
  name := "rrlToCore"
  args := [ "file" ]
  flags := [includeFlag]
  help := "Translate an RRL bicommand source file to Core and print it to stdout. \
    The output is ordinary Core concrete syntax: save it to a `.core.st` file \
    and drive its verification with `strata verify` directly."
  callback := fun v pflags => do
    let fm ← buildRRLDialectFileMap pflags
    let (pgm, ictx) ← readRRLProgram fm v[0]
    let (coreProgram, diagnostics) :=
      Strata.RRL.TranslateM.run (Strata.RRL.translateProgram pgm ictx)
    for d in diagnostics do
      IO.eprintln s!"{Message.format d (some ictx.fileMap)}"
    IO.println (StrataDDM.Program.toString (Strata.coreToStrataProgram coreProgram))

def rrlVerifyCommand : Command where
  name := "rrlVerify"
  args := [ "file" ]
  flags := includeFlag :: verifyOptionsFlags
  help := "Translate and verify an RRL bicommand source file (.rrl.st) directly, \
    without a separate rrlToCore + verify step."
  callback := fun v pflags => do
    let file := v[0]
    let opts ← parseVerifyOptions pflags { _root_.Core.VerifyOptions.default with verbose := .quiet }
      (inputFile := some file)
    let fm ← buildRRLDialectFileMap pflags
    let (pgm, ictx) ← readRRLProgram fm file
    let (vcResults, diagnostics) ← try
      Strata.RRL.verify pgm ictx opts
    catch e =>
      println! f!"{e}"
      IO.Process.exit ExitCode.internalError
    for d in diagnostics do
      IO.eprintln s!"{Message.format d (some ictx.fileMap)}"
    for vcResult in vcResults do
      let posStr := Imperative.MetaData.formatFileRangeD vcResult.obligation.metadata (some ictx.fileMap)
      println! f!"{posStr} [{vcResult.obligation.label}]: {vcResult.formatOutcome}"
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

end Strata.RRL.Cli
