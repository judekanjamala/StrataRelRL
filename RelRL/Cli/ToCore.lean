/-
  Copyright StrataRelRL Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module

public import RelRL.Cli.Common

public section

namespace Strata.RelRL.Cli

/-! # `relrl toCore`

```console
relrl toCore <file.relrl.st> [--include <dir>]...
```
Three stages: parse, `translate_program`, then `coreToStrataProgram` and DDM's
formatter, driven by the same `#dialect` declaration that parses Core.

**A printing quirk.** Primed names print two ways in the same output: `var |a'|`
in declarations and assignment targets, bare `a'` inside asserts. The asserts
are built directly as `Core.Expression.Expr` by `lower_rformula`; the
declarations go through Core's `renameLhs` and print via the binding printer,
which pipe-escapes the `'`. Both denote the same name and re-parse either way —
`'` is a valid identifier character in DDM's tokenizer — but it is worth knowing
before diffing two outputs by eye.

## Exit codes

| Code | Meaning | Trigger |
|---|---|---|
| 0 | printed | including when translation emitted a non-fatal diagnostic |
| 1 | user error | parse error, unreadable file, bad flag, or an error in the source program |
| 3 | `internalError` | a broken translator invariant |

The output still prints on a fatal diagnostic, but the exit code fails: printing
is the point of the command, and exiting 0 would hand a silently-wrong
`.core.st` file to whatever consumes it next. A non-fatal diagnostic prints to
stderr and still exits 0, so check stderr too if you script around it. -/

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
    report_diagnostics ictx diagnostics
    IO.println (StrataDDM.Program.toString (Strata.coreToStrataProgram coreProgram))
    -- Printing is the point, so the output still goes out — but a fatal
    -- diagnostic means it is not the program written, and exiting 0 would hand
    -- a silently-wrong Core file to whatever consumes it next.
    if diagnostics.any (fun d => d.kind.impact.isFatal) then
      IO.Process.exit (diagnostics_exit_code diagnostics)

end Strata.RelRL.Cli
