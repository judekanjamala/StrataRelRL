/-
  Copyright StrataRelRL Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import RRL.Cli

/-- Standalone `rrl` executable: a small, self-contained CLI for the RRL
dialect, independent of the unified `strata` binary (`Strata-CLI`). Reuses
`Strata.Cli.Framework` (from the `Strata` dependency) for flag parsing,
help text, and exit codes, matching the conventions of the main `strata`
CLI's commands without requiring RRL to depend on the separate
`Strata-CLI` package. -/
def commandGroups : List CommandGroup := [
  { name := "RRL"
    commands := [Strata.RRL.Cli.rrlToCoreCommand, Strata.RRL.Cli.rrlVerifyCommand]
    commonFlags := [] },
]

def commandList : List Command :=
  commandGroups.foldl (init := []) fun acc g => acc ++ g.commands

def commandMap : Std.HashMap String Command :=
  commandList.foldl (init := {}) fun m c => m.insert c.name c

def main (args : List String) : IO Unit :=
  runCommandMap commandMap commandGroups args
