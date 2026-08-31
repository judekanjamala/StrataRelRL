/-
  Copyright StrataRelRL Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module

import Lean.Parser.Extension

public import RelRL.Verify
public import Strata.Cli.Framework
public import StrataDDM.Util.IO
public import StrataDDM.BuiltinDialects

public section

namespace Strata.RelRL.Cli

/-! # Shared CLI plumbing

The three commands each live in their own module beside this one, each
documenting its own invocation, output and exit codes. What they share is here: getting a `.relrl.st` file parsed,
and turning translation diagnostics into output and an exit code.

Every command reuses `Strata.Cli.Framework`, as the built-in `Core`/`Laurel`
commands do. -/

/-- Preload `Core` and `RelRL` (plus DDM builtins) so `.relrl.st` files parse
without an `--include` search path.

Both dialects are compiled into the binary (`Grammar.lean`), and this hands them
to the parser as data. Selection is then per input file: the `program RelRL;`
header names the dialect, looked up by name in the preloaded `LoadedDialects`; a
miss falls through to the `DialectFileMap`, empty unless `--include` was passed,
and the run fails with `Unknown dialect …`.

`--include <dir>` is the one path that loads a dialect at run time, scanning for
`.dialect.st` files and registering them for lazy loading
(`StrataDDM/Elab/LoadedDialects.lean`). RelRL never needs it — its own dialect is
compiled in, so it is always found first. -/
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

/-- Diagnostics go to stderr with their source positions resolved. -/
def report_diagnostics (ictx : Lean.Parser.InputContext) (ds : Array Message) : IO Unit := do
  for d in ds do
    IO.eprintln s!"{Message.format d (some ictx.fileMap)}"

/-- What a run of diagnostics should exit with. An error in the user's program
exits 1; anything else a diagnostic reports is a translator bug, which exits 3
so it is not mistaken for a rejected program. -/
def diagnostics_exit_code (ds : Array Message) : UInt8 :=
  if ds.any (fun d => d.kind.impact != .userCodeError) then ExitCode.internalError
  else ExitCode.userError

end Strata.RelRL.Cli
