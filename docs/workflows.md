# Workflows

> **Scope.** How the workflows relate, and where each one is documented. Each
> command's invocation, output, exit codes and failure modes live in the module
> that implements it — this file points, it does not restate.

| Workflow | Command | Documented in |
|---|---|---|
| Build | `lake build relrl` | below |
| Verify | `relrl verify <file>` | `RelRL/Cli/Verify.lean` |
| Translate to Core | `relrl toCore <file>` | `RelRL/Cli/ToCore.lean` |
| Project one side | `relrl project <file> --side left\|right` | `RelRL/Cli/Project.lean` |

## How they relate

All three run-time workflows walk the same two stages and differ only in what
they do with the resulting `Core.Program`:

```
.relrl.st
   │
   │  ① parse            StrataDDM.readStrataText  ──►  StrataDDM.Program
   ▼                       Grammar.lean declares the dialect
   │  ② translate        translate_program_with
   │                       ├── .verify           ──►  one procedure, right side
   │                       │                          primed, spec as its contract
   │                       └── .project side   ──►  one side, unrenamed,
   ▼                                                  spec dropped
Core.Program
   │
   ├── verify   → Strata.Core.verifyProgram → SMT → one line per obligation
   ├── toCore   → print (both sides)
   └── project  → print (one side)
```

So `toCore` is `verify` stopped before the solver, and `project` is the same
pipeline in the other lowering mode. When an obligation fails and the reason is
not obvious, `toCore` shows the program the solver saw and `project` shows the
two programs the spec is talking about.

`Translate.lean`'s docstring maps stage 2 onto its six submodules;
`Verify.lean` is stage 3; `docs/design.md` argues the choices.

## Build

```console
lake build relrl          # library + `relrl` binary
lake exe relrl <cmd> …    # resolves and rebuilds, then runs
```

`lake exe` rebuilds before running, so it is the right entry point during
development; `./.lake/build/bin/relrl` runs whatever was built last. The
grammar is compiled in rather than read at run time — `Grammar.lean` says what
that means. `lakefile.toml` declares three targets: the `RelRL` library (the
default), `RelRLExamples` (which matches no Lean modules, since
`RelRL/Examples/` holds only `.relrl.st` files), and the `relrl` executable.

`CLAUDE.md` lists what bites when building: `warningAsError = true`, the
unpinned `Strata` dependency, and `//` rather than `--` inside `#dialect`.

## Regression baseline

There is no test target, so this table is the check: run `verify` over every
example and compare. A change to these counts is either a bug or a deliberate
change belonging in the same commit as this table.

| Example | Goals | Exercises |
|---|---|---|
| `Assertions.relrl.st` | 12/12 | every relational formula form, `requires` over a top-level constant |
| `SeqBi.relrl.st` | 4/4 | a bicommand sequence with an `Assert` between the aligned steps |
| `Swap.relrl.st` | 6/6 | the WhyRel swap port: unary calls related through the callees' specs, aligned two ways |
| `BiVar.relrl.st` | 4/4 | `Var` in all three forms, with and without a repeated name |
| `Branching.relrl.st` | 5/5 | `If` with and without `else`, and `If4`; the guard-agreement obligation |
| `Loops.relrl.st` | 20/20 | `While` lockstep and with alignment guards, `WhileL`, `WhileR`, `invariant` |
| `Params.relrl.st` | 4/4 | parameters and returns, symmetric and not, `inout` with `old`, a load-bearing `requires` |
| `BiCall.relrl.st` | 7/7 | `Call` on a `biproc`, twice in sequence over a bi-local, and once with the sides passing different arguments |

All eight exit 0 under `toCore` and under `project` on either side.

Nothing checks that `toCore` output re-parses; this repo does not build the
`strata` binary that would consume it.
