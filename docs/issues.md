# Known issues

> **Scope.** Defects in Strata or in this translation, each traced to its root
> cause and to what fixing it would take. Not a gap list: something RelRL simply
> does not implement yet, or a deliberate divergence from WhyRel, belongs in
> [`status.md`](status.md), which points here when the cause is a constraint
> that cannot be fixed.

## CLI help and error messages name `strata`, not `relrl`

`relrl --help`, `relrl <cmd> --help`, and any error path that falls back to the
framework's *default* hint print `strata` as the program name. Where
`RelRL/Cli.lean` passes an explicit hint — `project`'s two `--side` errors —
the name is right, which is the shape of the fix:

```console
$ relrl --help
Usage: strata <command> [flags]...

Command-line utilities for working with Strata.
...
$ relrl bogus
Exception: Expected subcommand, got bogus.

Run strata --help for additional help.
```

Hardcoded in `Strata.Cli.Framework` in four places: `printGlobalHelp` (usage
line and tagline), `printCommandHelp` (usage line), and the default hints of
`exitFailure` and `exitCmdFailure`. The framework takes no program-name
parameter. Cosmetic only — dispatch, flags and exit codes are correct.

The right fix is upstream: thread a `progName` through the help printers and
exit helpers, since every non-`strata` binary on this framework has the bug. A
local override in `Main.lean` works but is partial — `printIndented` and
`printFlag` are `private` and would need duplicating, and the two
`exitCmdFailure` paths inside `parseArgs` stay wrong unless `parseArgs` is
forked, risking drift from upstream's flag semantics.

## Translation assumes every non-`biproc` command is Core

`translate_program_with` builds the Core-only program with a hardcoded dialect
map:

```lean
let coreProgram := StrataDDM.Program.create Core_map "Core" coreCommands
```

`Core_map` holds Core, `Init` and Core's imports — not `RelRL`. Sound today
only by accident of the grammar: `biproc` is filtered out before reaching here,
and no bicommand is reachable at top level, so only Core operations arrive. That
breaks the moment RelRL gains a second top-level operator or imports a second
dialect.

Fix: thread the real dialect map — the one `build_relrl_dialect_file_map`
already builds — through `translate_program_with`, instead of naming
`Core_map`. Deferred until a second operator motivates it.

## `Agree x` is lexical, so nothing checks the name until Core does

`Agree x` is the one relational form whose operand is an `Ident` rather than a
Core expression: it has to name the *pair* `x`/`x'`, and `x'` is a name
translation invents, so it cannot be elaborated. It therefore emits `x == x'`
unconditionally, without consulting any scope.

That has one convenient consequence and one cost. The convenience: `Agree x`
works on a name a *split* declared, not just a bi-local, because a split's right
side is primed against its own declarations, so both `x` and `x'` exist in the
flattened block. The cost: a misspelling is caught only by Core, as a type error
against the translated program.

```console
$ relrl verify bogus.relrl.st          # ensures { Agree zzz }
bogus.relrl.st(26-47) ❌ Type checking error.
[assert [ensures_1] (zzz == zzz')] No free variables are allowed here!
Free Variables: [zzz, zzz']
```

`(26-47)` is a character range in the Core program, not a line and column in the
source, and the assert it prints is the lowered form rather than what was
written. Exit code 3.

Every other relational form — `Both (e)`, `<| e <]`, `[> e |>`, `l =:= r` — is a
real Core `bool` expression elaborated in the bi-local scope, so DDM checks those
names and reports at the right place:

```console
$ relrl verify splitexpr.relrl.st      # ensures { Both (a == 0) }, `a` split-declared
splitexpr.relrl.st(8, 16): Unknown expr identifier a
```

Narrowing the `Agree` case needs the translator to check its operand against the
names in scope — which it already computes, as `BodyState.bilocals`, plus each
split's own declarations — and report against the formula's source range, which
`lower_bicommand` already carries.

## DDM has one linear typing context

Every scoping limitation in RelRL comes from this. DDM threads a single linear
typing context through elaboration, and `@[scope(…)]` only chooses *which*
argument's context an operator exports — there is never more than one to export.

**A split's declarations cannot outlive it.** `bi_embed` carries no op-level
`@[scope(…)]`, so its result context is the one it was given, and
`Seq Bicommand` threads that unchanged onward:

```
biproc p =
  <<
    var a : int := 0;
  |
    var a : int := 0;
  >> ;
  <<
    var b : int := a;      // Unknown expr identifier a
  |
    var b : int := a;
  >> ;
```

Annotating it would not help: a split has two sides and one context to export,
and exporting the left's would make a later *right*-side reference resolve
against the left's binding. Hoisting into `|- … -|` or `Var` is the answer, and
between them they cover every case except the next one. The error is clean and
points at the source, so this is a limitation rather than a trap.

**The same name cannot be declared on both sides.** `bi_var` elaborates its
right `DeclList` in the left's context, so a repeated name pushes a second
binding and the two flatten to two `var n` in one Core block:

```console
$ relrl verify samename.relrl.st       # Var n : int | n : int ;
samename.relrl.st(64-71) ❌ Type checking error.
Variable n of type int already in context.
```

Caught, but by Core against the *translated* program — a character range rather
than a line and column, exit 3. `|- var n : int; -| ;` is the form for that
case. The cheap improvement is to reject the same-name `Var` in the translator,
against its own source range, with a message naming the synchronized form.

This is the one place RelRL cannot follow WhyRel's surface syntax, which writes
`Var i:int | i:int` routinely; `docs/status.md` records the mismatch.

**Assignment targets are not scope-checked**, which partly masks both. Core's
`Lhs` is `op lhsIdent (v : Ident)` and `Ident` is lexical, so a split side may
*assign* to a name it cannot *read*. The assignment still lands on the right
variable — priming is by syntactic side, not by resolution — but it is accepted
for a reason unrelated to it being correct.
