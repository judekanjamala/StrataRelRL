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

## A `datatype` silently misresolves every later top-level reference

**Unsound.** A `datatype` command anywhere above a `biproc` makes references to
top-level Core declarations inside that `biproc` resolve to the wrong
declaration, or to none at all. A reference that lands out of range becomes the
default `Core.Decl`, which lowers to the literal `0` — so a false spec verifies:

```console
$ cat unsound.relrl.st
datatype Box { BoxInt (ival : int) };
const k : int := 5;
biproc t
  ensures { <| a == 0 <] }        // false: a is k, which is 5
=
  |- var a : int; -| ;
  << a := k; | a := k; >> ;

$ relrl verify unsound.relrl.st
All 1 goals passed.               # exit 0
```

`toCore` shows the substitution directly — `a := k` came out as `a := 0`:

```
biproc: { var a : int; a := 0; var |a'| : int; |a'| := 0; assert [ensures_1]: a == 0; }
```

Delete the `datatype` line and the same file behaves correctly.

The root cause is in `translate_program_with`, which reconstructs Core's
top-level binding list from the decls `translateCoreDecls` returns:

```lean
let top : TransBindings := { freeVars := coreDecls.toArray }
```

That assumes one `freeVars` entry per returned decl. `translateCoreDecls`
pushes exactly one decl per *command*, but two of its branches grow `freeVars`
by more:

| Command | decls returned | `freeVars` entries added |
|---|---|---|
| `command_datatypes` | 1 | per datatype: the type, then every constructor, tester, field accessor and unsafe field accessor |
| `command_recfndefs` | 1 | one per function in the block |

Every other branch is 1:1, which is why the defect stayed hidden — no example
uses either command. A `.fvar i` in a `biproc` body indexes DDM's global
context, so from the first such command onward `top.freeVars` is shorter than
the index space and every later index is off. Core's `translateExpr` asserts
`i < bindings.freeVars.size`, so the run prints a `PANIC` and a backtrace per
misresolved reference — to **stderr**, where RelRL's CLI does not collect it,
leaving the exit code to report an ordinary verification result.

The same expressions are fine through a plain Core `procedure` in the same
file, since those go to `translateCoreDecls` directly and never touch the
reconstructed list.

**Contained, not fixed.** `misaligning_command?` in `Translate.lean` names the
two offending commands, and `translate_program_with` refuses the file rather
than lowering a body against a `top` it knows is short:

```console
$ relrl verify unsound.relrl.st
unsound.relrl.st(2, (0-37)) a `datatype` declaration cannot appear in a file that
also declares a `biproc`: references to top-level declarations inside the biproc
would silently resolve to the wrong one. docs/issues.md has the mechanism.
Finished with 0 goals checked, but 1 error(s) occurred.   # exit 1
```

No body is lowered once it fires — lowering one anyway trips Core's `assert!`
and buries the message under backtraces. The guard is exact, not conservative:
a `datatype` in a file with no `biproc` still works (that path never touches the
reconstructed list), as do a type synonym, an opaque `type`, and a
*single*-function `rec` block, all of which are 1:1.

The real fix is upstream: have `translateCoreDecls` return its final
`TransBindings` alongside the decls — it holds them at the end already — and
have `translate_program_with` use that as `top`. That is correct for every
command, present and future, and lets the guard be deleted. The dependency is
unpinned (`rev = "main"`), so it is a patch upstream rather than a fork.

Do not fix it by reimplementing `translateCoreDecls`'s dispatch inside RelRL:
that duplicates a thirteen-case match against an unpinned dependency, which is
the drift CLAUDE.md warns about.

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
between them they cover every case. The error is clean and points at the source,
so this is a limitation rather than a trap.

**Assignment targets are not scope-checked**, which partly masks it. Core's
`Lhs` is `op lhsIdent (v : Ident)` and `Ident` is lexical, so a split side may
*assign* to a name it cannot *read*. Priming is by syntactic side, so a
right-side assignment to a *bi-local* still lands on the right copy; the case
below is what escapes.

## A right-side fragment can name a left-only variable

`prime_expr` and `prime_stmts` rename a right-hand fragment against a
whitelist — the bi-local set — so a name outside it passes through untouched.
That is right for a top-level Core declaration, which both programs share, and
wrong for a variable `Var acc : int | ;` gave the left program alone:

```console
$ cat unsound.relrl.st
biproc unsound
  ensures { <| acc == 6 <] }        // a claim about the LEFT state
=
  Var acc : int | ;
  << acc := 0; | acc := 6; >> ;

$ relrl verify unsound.relrl.st
All 1 goals passed.
```

The right program has no `acc`, yet its write is the one that discharges a
left-state obligation: both sides resolved to the same Core variable. The
symmetric direction — a left fragment naming a right-only variable — is caught,
since a left fragment is never primed and the right's name carries the prime, so
Core sees an undeclared variable.

Closing it means priming a right-side fragment against a *blacklist* instead:
rename every free name except the program's top-level Core declarations, which
is exactly the set `TransBindings.freeVars` already holds at `lower_biproc`'s
entry. What that needs first is knowing which names a fragment binds itself,
which is the scope check Core's lexical `Lhs` does not do.
