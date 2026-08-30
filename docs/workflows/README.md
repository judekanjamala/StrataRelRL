# Workflows

> **Scope.** One file per workflow, plus [`pipeline.md`](pipeline.md) for the
> stages they share. Each workflow file covers invocation, output, exit codes
> and failure modes for *that command only*; shared machinery goes in
> `pipeline.md`, and the reasoning behind it in
> [`../design.md`](../design.md).



| Workflow | Command | File |
|---|---|---|
| Build | `lake build relrl` | [`build.md`](build.md) |
| Verify | `relrl verify <file>` | [`verify.md`](verify.md) |
| Translate to Core | `relrl toCore <file>` | [`toCore.md`](toCore.md) |
| Project one side | `relrl project <file> --side left\|right` | [`project.md`](project.md) |

[`pipeline.md`](pipeline.md) documents the stages the three run-time workflows
share, in depth: parsing, the self-composition lowering, and Core verification.
Read it once; the per-workflow files reference it rather than repeat it.

## How they relate

All three run-time workflows walk the same first two stages and differ only in
what they do with the resulting `Core.Program`:

```
.relrl.st
   │
   │  ① parse            StrataDDM.readStrataText  ──►  StrataDDM.Program
   ▼
   │  ② translate        translate_program_with
   │                       ├── .verify           ──►  one procedure, right side
   │                       │                          primed, ensures as asserts
   │                       └── .project side   ──►  one side, unrenamed,
   ▼                                                  ensures dropped
Core.Program
   │
   ├── verify   → Strata.Core.verifyProgram → SMT → one line per obligation
   ├── toCore   → print (self-composition)
   └── project  → print (one side)
```

So `toCore` is `verify` stopped before the solver, and `project` is the same
pipeline with the other lowering mode. If an obligation fails under `verify` and
the reason is not obvious, `toCore` shows the program the solver saw and
`project` shows the two programs the spec is talking about.

## Not yet a workflow

- **No test target.** `RelRLTest/` was removed; the regression check is running
  `relrl verify` over `RelRL/Examples/` and comparing goal counts against the
  table in [`verify.md`](verify.md).
- **No round-trip check.** Nothing verifies that `toCore` output re-parses, and
  this repo does not build the `strata` binary that would consume it.
