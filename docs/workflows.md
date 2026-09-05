# Workflows

> **Scope.** How the workflows relate, and where each one is documented. Each
> command's invocation, output, exit codes and failure modes live in the module
> that implements it, and the examples in `RelRL/Examples/README.md` — this file
> points, it does not restate.

| Workflow | Command | Documented in |
|---|---|---|
| Build | `lake build relrl` | below |
| Verify | `relrl verify <file>` | `RelRL/Cli/Verify.lean` |
| Translate to Core | `relrl toCore <file>` | `RelRL/Cli/ToCore.lean` |
| Project one side | `relrl project <file> --side left\|right` | `RelRL/Cli/Project.lean` |

## How they relate

All three walk the same three stages and differ only in what they do with the
resulting `Core.Program`:

```
.relrl.st
   │
   │  ① parse            StrataDDM.readStrataText  ──►  StrataDDM.Program
   │                       Grammar.lean declares the dialect
   │
   │  ② desugar          desugar_program           ──►  StrataDDM.Program
   ▼                       Desugar.lean; biproc bodies only
   │  ③ translate        translate_program_with
   │                       ├── .compose          ──►  one procedure, right side
   │                       │                          primed, spec as its contract
   │                       └── .project side   ──►  one side, unrenamed,
   ▼                                                  spec dropped
Core.Program
   │
   ├── verify   → Strata.Core.verifyProgram → SMT → one line per obligation
   ├── toCore   → print (Composition)
   └── project  → print (one side)
```

So `toCore` is `verify` stopped before the solver, and `project` is the same
pipeline in the other lowering mode. When an obligation fails and the reason is
not obvious, `toCore` shows the program the solver saw and `project` the two
programs the spec is talking about.

Stage ② runs inside `translate_program_with`, so every workflow gets it, and so
does `bi_while`'s own re-lowering of its body. `Translate.lean`'s docstring maps
stage ③ onto its six submodules; [`design.md`](design.md) argues the choices.

## Build

```console
lake build relrl          # library + `relrl` binary
lake exe relrl <cmd> …    # resolves and rebuilds, then runs
```

`lake exe` rebuilds before running, so it is the right entry point during
development; `./.lake/build/bin/relrl` runs whatever was built last. The grammar
is compiled in rather than read at run time — `Grammar.lean` says what that
means. `lakefile.toml` declares three targets: the `RelRL` library (the default),
`RelRLExamples` (which matches no Lean modules — `RelRL/Examples/` holds only
`.relrl.st` files and a `README.md`), and the `relrl` executable.

`CLAUDE.md` lists what bites when building: `warningAsError = true`, the unpinned
`Strata` dependency, and `//` rather than `--` inside `#dialect`.

## Regression baseline

[`RelRL/Examples/README.md`](../RelRL/Examples/README.md) lists every example,
its expected goal count, and what it exercises. There is no test target, so that
table is the check.
