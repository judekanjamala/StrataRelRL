/-
  Copyright StrataRelRL Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module

public import RelRL.Cli.Common
public import RelRL.Cli.ToCore
public import RelRL.Cli.Project
public import RelRL.Cli.Verify

/-! # RelRL CLI

One module per command, each documenting itself. `Main.lean` assembles them
into the `relrl` binary; `RelRL.Cli.Common` holds what all three share. -/
