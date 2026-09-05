# Examples

> **Scope.** Every `.relrl.st` example, what it exercises, and the goal count it
> must produce. This is the regression baseline — there is no test target, so
> this table is the check. A change to a count is either a bug or a deliberate
> change belonging in the same commit as this file.

Run one with `lake exe relrl verify RelRL/Examples/<file>`;
[`docs/workflows.md`](../../docs/workflows.md) relates `verify` to `toCore` and
`project`.

## Dialect examples, one per feature

| Example | Goals | Exercises |
|---|---|---|
| `Assertions.relrl.st` | 23/23 | every relational formula form, `requires` over a top-level constant |
| `SeqBi.relrl.st` | 5/5 | a bicommand sequence with an `Assert` between the aligned steps |
| `Swap.relrl.st` | 6/6 | the WhyRel swap port: unary calls related through the callees' specs, aligned two ways |
| `BiVar.relrl.st` | 4/4 | `Var` in all three forms, with and without a repeated name |
| `Branching.relrl.st` | 5/5 | `If` with and without `else`, and `If4`; the guard-agreement obligation |
| `Loops.relrl.st` | 20/20 | `While` lockstep and with alignment guards, `WhileL`, `WhileR`, `invariant` |
| `Params.relrl.st` | 5/5 | parameters and returns, symmetric and not, `inout` with `old`, a load-bearing `requires` |
| `BiCall.relrl.st` | 7/7 | `Call` on a `biproc`, twice in sequence over a bi-local, and once with the sides passing different arguments |

`Assertions.relrl.st` is the per-form catalogue and doubles as the smoke test;
every other example carries a ~3-line header saying what it demonstrates and
where the reasoning lives.

## WhyRel case studies

Under `WhyRel/`, ported from `dnaumann/RelRL`'s `examples/all_all`. The last two
reason about map *equality*, so they need `--use-array-theory` — `CLAUDE.md` says
why.

| Example | Goals | Exercises |
|---|---|---|
| `WhyRel/Factorial.relrl.st` | 15/15 | alignment guards `<\| false <]`, an `invariant` relating the two counters |
| `WhyRel/EquivCheck.relrl.st` | 18/18 | a Core `while` nested inside a split's side |
| `WhyRel/MonoFact.relrl.st` | 11/11 | `Let` for a cross-side inequality; a one-sided alignment guard |
| `WhyRel/Majorization.relrl.st` | 10/10 | real alignment guards, discharging the `If` guard-agreement obligation |
| `WhyRel/FizzBuzzSum.relrl.st` | 23/23 | an uninterpreted `function` with axioms over a `Map` |
| `WhyRel/FizzBuzz.relrl.st` | 21/21 | `inout Map int int`; needs `--use-array-theory` |
| `WhyRel/SimpleIO.relrl.st` | 29/29 | a nested `Map` type synonym, `old` in an invariant; needs `--use-array-theory` |

Which WhyRel case studies are *not* here, and why, is
[`docs/status.md`](../../docs/status.md)'s: everything left needs a heap.

All fifteen exit 0 under `toCore` and under `project` on either side. Nothing
checks that `toCore` output re-parses; this repo does not build the `strata`
binary that would consume it.
