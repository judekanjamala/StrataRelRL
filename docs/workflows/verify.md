# Verify

> **Scope.** `relrl verify` only — its output, exit codes and failure modes.
> Translation stages are in [`pipeline.md`](pipeline.md).

```console
relrl verify <file.relrl.st> [--include <dir>]... [verify options]
```

Parse, translate by self-composition, and discharge every proof obligation in
one step. Prints one line per obligation, then a summary. Needs an SMT solver on
`PATH` (cvc5 by default).

Defined at `verify_command` in `RelRL/Cli.lean`; the translation and
verification stages themselves are [`pipeline.md`](pipeline.md) §2 and §3.

## Stages

1. `build_relrl_dialect_file_map` → `read_relrl_program` — parse to
   `StrataDDM.Program` ([`pipeline.md`](pipeline.md) §1).
2. `translate_program` — self-composition lowering to `Core.Program`
   ([`pipeline.md`](pipeline.md) §2). The two sides are flattened into one
   procedure, the right side's top-level locals primed, and each `ensures` spec
   becomes a Core `assert` after both sides have run.
3. `Strata.Core.verifyProgram` — Core's own VC generation and SMT discharge,
   unmodified ([`pipeline.md`](pipeline.md) §3).

Because step 3 is Core's unmodified pipeline, every obligation reported is an
ordinary Core assertion. What makes it *relational* is entirely what step 2
built.

## Output

```console
$ relrl verify RelRL/Examples/Assertions.relrl.st
Assertions.relrl.st(43, 2) [assert_1_1]: ✅ pass
Assertions.relrl.st(43, 2) [assert_1_2]: ✅ pass
Assertions.relrl.st(18, 2) [ensures_1]: ✅ pass
Assertions.relrl.st(18, 2) [ensures_2]: ✅ pass
Assertions.relrl.st(18, 2) [ensures_3]: ✅ pass
Assertions.relrl.st(18, 2) [ensures_4]: ✅ pass
Assertions.relrl.st(18, 2) [ensures_5]: ✅ pass
Assertions.relrl.st(18, 2) [ensures_6]: ✅ pass
Assertions.relrl.st(18, 2) [ensures_7]: ✅ pass
Assertions.relrl.st(18, 2) [ensures_8]: ✅ pass
Assertions.relrl.st(18, 2) [ensures_9]: ✅ pass
Assertions.relrl.st(18, 2) [ensures_10]: ✅ pass
All 12 goals passed.
```

The position is the formula's own source range. Labels are synthesised —
`ensures_<n>` for the trailing clause, `assert_<k>_<n>` for the k-th
`Assert { R }` — because a relational formula carries no label of its own, and
`<n>` counts the conjuncts a top-level `/\` was split into — so the ten
conjuncts of the `ensures` clause plus the two of the `Assert` make twelve
obligations from two written formulas.

**A spec that does not hold.** Reported per obligation, exit 2. Here
`Swap.relrl.st`'s second bicommand has been changed to end `a := 4` on the
right, so `Agree a` is false while `Agree b` still holds:

```console
$ relrl verify fail.relrl.st
fail.relrl.st(9, 2) [ensures_1]: ❌ fail
fail.relrl.st(9, 2) [ensures_2]: ✅ pass
Finished with 1 goals passed, 1 failed.
```

**A name a spec got wrong.** `Agree x` is lexical, so nothing checks it until
Core does — against the *translated* program, so the position is a character
range in the Core text rather than a line and column in the source, and the
assert printed is the lowered form. Exit 3:

```console
$ relrl verify bogus.relrl.st        # ensures { Agree zzz }
bogus.relrl.st(26-47) ❌ Type checking error.
[assert [ensures_1] (zzz == zzz')] No free variables are allowed here!
Free Variables: [zzz, zzz']
```

Every other relational form is a real Core expression elaborated in the
bi-local scope, so a bad name there is caught by DDM at the right source
position instead. See `docs/issues.md`.

**A parse error.** Reported against the source with a line and column, exit 1.
Here the synchronized bicommand was closed with WhyRel's `_|` rather than
RelRL's `-|`:

```console
$ relrl verify bad.relrl.st
Exception: 1 error(s) reading bad.relrl.st:
  6:17: unexpected identifier; expected '-| ;'


Run strata --help for additional help.
```

## Regression baseline

There is no test target, so this table is the regression check: run `verify` over
every example and compare. Any change to these counts is either a bug or a
deliberate change that belongs in the same commit as this table.

| Example | Goals | Exit | Exercises |
|---|---|---|---|
| `Assertions.relrl.st` | 12/12 pass | 0 | every relational formula form, `requires` over a top-level constant |
| `SeqBi.relrl.st` | 4/4 pass | 0 | a bicommand sequence with an `Assert` between the aligned steps |
| `Swap.relrl.st` | 2/2 pass | 0 | the WhyRel swap port: synchronized declarations, a two-step alignment |
| `BiVar.relrl.st` | 2/2 pass | 0 | `Var` in all three forms, against the shared-name `\|- … -\|` |

`toCore` and `project --side left|right` should exit 0 on all four.

## Flags

`--include <dir>` (repeatable) plus Core's `verifyOptionsFlags` — solver
selection, timeouts, VC dump directory, verbosity. `verify` overrides the
default verbosity to `.quiet` so the per-obligation lines are the whole output.

## Debugging a failure

`verify` gives you the verdict; it does not show you the program that was
checked. When an obligation fails and the reason is not obvious, run
[`toCore`](toCore.md) on the same file to see the self-composed Core program
the solver actually saw, and [`project`](project.md) to check each side in
isolation.
