/-
  Copyright StrataRelRL Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import RelRL.Cli

/-- Standalone `relrl` executable: a small, self-contained CLI for the RelRL
dialect, independent of the unified `strata` binary (`Strata-CLI`). Reuses
`Strata.Cli.Framework` (from the `Strata` dependency) for flag parsing,
help text, and exit codes, matching the conventions of the main `strata`
CLI's commands without requiring RelRL to depend on the separate
`Strata-CLI` package. -/
def commandGroups : List CommandGroup := [
  { name := "RelRL"
    commands := [Strata.RelRL.Cli.relrlToCoreCommand, Strata.RelRL.Cli.relrlVerifyCommand]
    commonFlags := [] },
]

def commandList : List Command :=
  commandGroups.foldl (init := []) fun acc g => acc ++ g.commands

def commandMap : Std.HashMap String Command :=
  commandList.foldl (init := {}) fun m c => m.insert c.name c

def main (args : List String) : IO Unit :=
  runCommandMap commandMap commandGroups args
