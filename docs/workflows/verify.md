# Verify

> **Scope.** `relrl verify` only — its output, exit codes and failure modes.
> Translation stages are in [`pipeline.md`](pipeline.md).

```console
relrl verify <file.relrl.st> [--include <dir>]... [verify options]
```

Parse, translate by self-composition, and discharge every proof obligation in
one step. Prints one line per obligation, then a summary. Needs an SMT solver on
`PATH` (cvc5 by default).

Defined at `verify_command` in `RelRL/Cli/Verify.lean`; the translation and
verification stages themselves are [`pipeline.md`](pipeline.md) §2 and §3.

## Stages

1. `build_relrl_dialect_file_map` → `read_relrl_program` — parse to
   `StrataDDM.Program` ([`pipeline.md`](pipeline.md) §1).
2. `translate_program` — self-composition lowering to `Core.Program`
   ([`pipeline.md`](pipeline.md) §2). The two sides are flattened into one
   procedure, every right-side variable primed, and each `ensures` spec becomes
   a Core `assert` after both sides have run.
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
`SeqBi.relrl.st`'s first bicommand has been changed to set `a := 4` on the
right, so every claim about `a` is false while the ones about `b` still hold —
the mid-body `Assert` and the `ensures` both split, so four obligations report
independently:

```console
$ relrl verify fail.relrl.st
fail.relrl.st(18, 2) [assert_1_1]: ❌ fail
fail.relrl.st(18, 2) [assert_1_2]: ✅ pass
fail.relrl.st(8, 2) [ensures_1]: ❌ fail
fail.relrl.st(8, 2) [ensures_2]: ✅ pass
Finished with 2 goals passed, 2 failed.
```

Each line is one conjunct, at the source position of the clause it came from —
the `Assert`'s two at line 18, the `ensures`'s two at line 8.

**A name a spec got wrong.** Reported against the clause, exit 1. `Agree x`
takes an `Ident` rather than an expression, so DDM does not elaborate it
(`docs/design.md`); the translator checks the operand against what each side
declared, and says which program is missing it:

```console
$ relrl verify bogus.relrl.st        # ensures { Agree zzz }
bogus.relrl.st(3, (2-23)) `zzz` is not a variable of the left program
bogus.relrl.st(3, (2-23)) `zzz` is not a variable of the right program
Finished with 0 goals checked, but 2 error(s) occurred.
```

Every other relational form is a real Core expression elaborated in the scope
the formula sits in, so DDM catches a bad name there first, at the same source
position.

**A name declared twice.** Both programs land in one Core scope, so a name has
to be unique there — under its Core name, which for the
right program carries the prime. The translator checks this itself and reports
against the declaration, exit 1; verification is skipped, since the Core program
would not be the one the source denotes:

```console
$ relrl verify dup.relrl.st          # |- var a : int; -| ; then Var a : int | ;
dup.relrl.st(7, (6-13)) `a` is declared twice in the left program
Finished with 0 goals checked, but 1 error(s) occurred.
```

A collision between a written prime and a generated one reads the same way:
`Var n' : int | n : int ;` reports that `n` in the right program collides with
`n'` in the left, since self-composition names both `n'`. Note what is *not* an
error: `Var n : int | n : int ;` declares `n` and `n'`, one per program, and is
fine.

**A `datatype` or multi-function `rec` block beside a `biproc`.** Refused
against the offending command, exit 1. The two cannot share a file: the biproc
body's references to top-level declarations would silently resolve to the wrong
declaration — [`issues.md`](../issues.md) has the mechanism and the upstream fix.

```console
$ relrl verify dt.relrl.st
dt.relrl.st(2, (0-37)) a `datatype` declaration cannot appear in a file that also
declares a `biproc`: references to top-level declarations inside the biproc would
silently resolve to the wrong one. docs/issues.md has the mechanism.
Finished with 0 goals checked, but 1 error(s) occurred.
```

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
| `Swap.relrl.st` | 6/6 pass | 0 | the WhyRel swap port: unary calls related through the callees' specs, aligned two ways |
| `BiVar.relrl.st` | 4/4 pass | 0 | `Var` in all three forms, with and without a repeated name, against `\|- … -\|` |
| `Branching.relrl.st` | 5/5 pass | 0 | `If` with and without `else`, and `If4`; the guard-agreement obligation |
| `Loops.relrl.st` | 20/20 pass | 0 | `While` lockstep and with alignment guards, `WhileL`, `WhileR`, `invariant` |
| `Params.relrl.st` | 3/3 pass | 0 | parameters and returns, symmetric and not, `inout`, a load-bearing `requires` |

`toCore` and `project --side left|right` should exit 0 on all seven.

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
