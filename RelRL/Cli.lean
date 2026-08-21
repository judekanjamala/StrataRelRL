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

Two ways to drive verification of an RelRL bicommand program from the
command line, both reusing the unified `strata` CLI's framework
(`Strata.Cli.Framework`) the same way `StrataPython.Cli` and the built-in
`Core`/`Laurel` commands do:

- `relrlVerify <file>`: parse, translate, and verify an RelRL `.relrl.st` file in
  one step, printing one pass/fail line per proof obligation (mirroring the
  generic `verify` command's output and exit-code scheme).
- `relrlToCore <file>`: translate an RelRL `.relrl.st` file to Core concrete
  syntax and print it to stdout. The output is a normal `.core.st` file, so
  it can be saved and verified with the *generic* `strata verify` command
  (`Core.verify`/`Core.verifyProgram`) without any RelRL-specific tooling —
  i.e., RelRL→Core translation and Core verification are decoupled, just like
  `laurelToCore` decouples Laurel translation from Core verification. -/

/-- Preload the `Core` and `RelRL` dialects (plus DDM builtins) so that
`.relrl.st` files can be parsed without a separate `--include` search path. -/
def buildRelRLDialectFileMap (pflags : ParsedFlags) : IO StrataDDM.DialectFileMap := do
  let preloaded := StrataDDM.Elab.LoadedDialects.builtin
    |>.addDialect! Strata.Core
    |>.addDialect! Strata.RelRL
  let mut fm ← StrataDDM.DialectFileMap.new preloaded
  for path in pflags.getRepeated "include" do
    match ← fm.add path |>.toBaseIO with
    | .error msg => exitFailure msg
    | .ok fm' => fm := fm'
  return fm

/-- Read and parse an RelRL program file via the DDM API, the same way the
unified `strata` binary's `readStrataProgram` helper reads any other
dialect's file. -/
def readRelRLProgram (fm : StrataDDM.DialectFileMap) (file : String) :
    IO (StrataDDM.Program × Lean.Parser.InputContext) := do
  let text ← StrataDDM.Util.readInputSource file
  let displayPath := StrataDDM.Util.displayName file
  let inputCtx := Lean.Parser.mkInputContext text displayPath
  match ← StrataDDM.readStrataText fm displayPath text.toUTF8 with
  | .program pgm => pure (pgm, inputCtx)
  | .dialect _ => throw (IO.userError s!"Expected an RelRL program file, got a dialect: {file}")

def relrlToCoreCommand : Command where
  name := "relrlToCore"
  args := [ "file" ]
  flags := [includeFlag]
  help := "Translate an RelRL bicommand source file to Core and print it to stdout. \
    The output is ordinary Core concrete syntax: save it to a `.core.st` file \
    and drive its verification with `strata verify` directly."
  callback := fun v pflags => do
    let fm ← buildRelRLDialectFileMap pflags
    let (pgm, ictx) ← readRelRLProgram fm v[0]
    let (coreProgram, diagnostics) :=
      Strata.RelRL.TranslateM.run (Strata.RelRL.translateProgram pgm ictx)
    for d in diagnostics do
      IO.eprintln s!"{Message.format d (some ictx.fileMap)}"
    IO.println (StrataDDM.Program.toString (Strata.coreToStrataProgram coreProgram))

def relrlVerifyCommand : Command where
  name := "relrlVerify"
  args := [ "file" ]
  flags := includeFlag :: verifyOptionsFlags
  help := "Translate and verify an RelRL bicommand source file (.relrl.st) directly, \
    without a separate relrlToCore + verify step."
  callback := fun v pflags => do
    let file := v[0]
    let opts ← parseVerifyOptions pflags { _root_.Core.VerifyOptions.default with verbose := .quiet }
      (inputFile := some file)
    let fm ← buildRelRLDialectFileMap pflags
    let (pgm, ictx) ← readRelRLProgram fm file
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
