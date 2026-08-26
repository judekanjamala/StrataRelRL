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
def command_groups : List CommandGroup := [
  { name := "RelRL"
    commands := [Strata.RelRL.Cli.to_core_command, Strata.RelRL.Cli.verify_command]
    commonFlags := [] },
]

def command_list : List Command :=
  command_groups.foldl (init := []) fun acc g => acc ++ g.commands

def command_map : Std.HashMap String Command :=
  command_list.foldl (init := {}) fun m c => m.insert c.name c

-- Note: the framework's help and error output hardcodes the program name
-- `strata`, so `relrl --help` misnames this binary. See docs/issues.md.
def main (args : List String) : IO Unit :=
  runCommandMap command_map command_groups args
