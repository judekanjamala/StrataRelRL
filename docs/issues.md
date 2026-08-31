# Known issues

> **Scope.** Defects in Strata or in this translation, each traced to its root
> cause and to what fixing it would take. Not a gap list: something RelRL simply
> does not implement yet, or a deliberate divergence from WhyRel, belongs in
> [`status.md`](status.md), which points here when the cause is a constraint
> that cannot be fixed.

## CLI help and error messages name `strata`, not `relrl`

`relrl --help`, `relrl <cmd> --help`, and any error path that falls back to the
framework's *default* hint print `strata` as the program name. Where
`RelRL/Cli/Project.lean` passes an explicit hint — its two `--side` errors —
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

## A `datatype` breaks the top-level binding list a `biproc` body resolves against

`translate_program_with` reconstructs Core's top-level binding list from the
decls `translateCoreDecls` returns:

```lean
let top : TransBindings := { freeVars := coreDecls.toArray }
```

That assumes one `freeVars` entry per returned decl. `translateCoreDecls` pushes
exactly one decl per *command*, but two of its branches grow `freeVars` by more:

| Command | decls returned | `freeVars` entries added |
|---|---|---|
| `command_datatypes` | 1 | per datatype: the type, then every constructor, tester, field accessor and unsafe field accessor |
| `command_recfndefs` | 1 | one per function in the block |

Every other branch is 1:1. A `.fvar i` in a `biproc` body indexes DDM's global
context, so from the first such command onward `top.freeVars` is shorter than
the index space and every later index is off. An index that lands out of range
yields the default `Core.Decl`, which lowers to the literal `0` — a reference to
a top-level constant becomes `0`, and a false spec can verify. Core's
`translateExpr` asserts `i < bindings.freeVars.size`, so such a run also prints
a `PANIC` per misresolved reference to **stderr**, where RelRL's CLI does not
collect it.

**Contained.** `misaligning_command?` names the two offending commands, and
`translate_program_with` refuses the file rather than lowering a body against a
`top` it knows is short:

```console
$ relrl verify dt.relrl.st
dt.relrl.st(2, (0-37)) a `datatype` declaration cannot appear in a file that also
declares a `biproc`: references to top-level declarations inside the biproc would
silently resolve to the wrong one. docs/issues.md has the mechanism.
Finished with 0 goals checked, but 1 error(s) occurred.   # exit 1
```

No body is lowered once it fires, so Core's `assert!` is never reached and the
message stands alone. The guard is exact, not conservative: a `datatype` in a
file with no `biproc` still works — that path goes through `translateCoreDecls`
directly and never touches the reconstructed list — as do a type synonym, an
opaque `type`, and a *single*-function `rec` block, all of which are 1:1.

The fix is upstream: have `translateCoreDecls` return its final `TransBindings`
alongside the decls — it holds them at the end already — and have
`translate_program_with` use that as `top`. That is correct for every command,
present and future, and lets the guard be deleted. The dependency is unpinned
(`rev = "main"`), so it is a patch upstream rather than a fork.

Do not fix it by reimplementing `translateCoreDecls`'s dispatch inside RelRL:
that duplicates a thirteen-case match against an unpinned dependency, which is
the drift CLAUDE.md warns about.

## DDM has one linear typing context

DDM threads a single linear typing context through elaboration, and
`@[scope(…)]` only chooses *which* argument's context an operator exports —
there is never more than one to export. A bicommand has two sides, so DDM cannot
tell which program a reference belongs to: `Var n : int | n : int ;` and
`<< var n : int; | var n : int; >> ;` each push two bindings named `n`, and a
reference to `n` resolves to one of them whichever side of the `|` it sits on.

That costs nothing on its own, because priming is applied by syntactic side
after elaboration: the reference resolves to a binding *named* `n` either way,
and a right-hand fragment renames it to `n'`. What DDM cannot do is reject a
side that names the *other* program's variable. Core's `Lhs` is
`op lhsIdent (v : Ident)` and `Ident` is lexical, so a split side may even
*assign* to a name it cannot read. `BodyState.check_side` in the translator is
what reports that, with the source range DDM would have used.
