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

## A top-level declaration is shared by both programs

**Unsound against WhyRel's semantics.** WhyRel gives each side its own state, so
a global is two variables and the two programs may differ in it. Here a `const`
is one symbol that both sides read, which makes agreement on anything derived
from it free:

```console
$ cat glob.relrl.st
const g : int;
biproc p (out r : int) | (out r : int)
  ensures { Agree r }
=
  << r := g; | r := g; >> ;

$ relrl toCore glob.relrl.st       # r := g;  |r'| := g;   -- one `g`
$ relrl verify glob.relrl.st
All 1 goals passed.
```

`Agree r` should not be provable: nothing relates the two programs' `g`. Each
should get its own copy, `g` and `g'`, as every bi-local does.

The cause is that a Core constant is a 0-ary *function*, so a reference to it
lowers to `.op "g"` and never to `.fvar "g"`. Every priming helper is built on
`substFvar`, and every traversal in `Strata/DL/Lambda` passes `.op` through
unchanged — there is no substitution over operator names anywhere in Lambda or
Core (`NameMangling` is about monomorphization). Globals are therefore invisible
to priming, and equally invisible to `fragment_names`, so `check_side` does not
see them either.

Fixing it has two halves. **Duplicate the declarations**: a `const` or function
gets a primed copy, an `axiom` and a `distinct` get one with their references
primed — otherwise `g'` is unconstrained while `g` is not — and a `procedure`
gets one, since in WhyRel each side has its own. A `type` or `datatype` does not:
a type is not program state.

**Then rename references on the right**, for which there are two routes:

- write an op-renaming traversal over `LExpr` and `Statement` — about thirty
  lines, and the first traversal of Core's AST this translator would own; or
- lower right-hand fragments against a *primed binding set*, a copy of the
  top-level `TransBindings` with each declaration's name primed, so
  `translateExpr` emits `.op "g'"` directly. That needs `bi_sync` to lower its
  one statement twice, once per binding set, rather than once with a lexical
  rename after.

The first is contained and leaves the lexical-priming design intact; the second
avoids a new traversal but reworks how priming is applied.

## Sibling blocks sharing a declared name lose every obligation

Two Core blocks at the same level declaring the same name make Core's verifier
return **no obligations at all** for the enclosing procedure, silently and with
exit 0. This is Core's, not RelRL's — here is a repro with no bicommands in it:

```console
$ cat sib.relrl.st
program Core;
procedure m (out r : int, out s : int)
  spec { ensures r == 1; }
{
  if (true) { var y : int := 1; r := y; }
  if (true) { var y : int := 5; s := y; }
};
$ relrl verify sib.relrl.st
All 0 goals passed.                      # exit 0
```

Rename the second `y` to `z` and the `ensures` comes back as a checked
obligation that passes. Nothing is printed on stdout or stderr in the colliding
case: the clause is not reported as failing, unknown, or skipped — it is simply
absent, so a passing run means nothing. That is the worst available failure
mode, and it is reachable from a hand-written Core file.

Two things narrow it. `--verbose` shows `Type checking succeeded.` and then an
empty `VCs:` list, so the program is accepted and it is VC *generation* that
emits nothing — not the typechecker rejecting the second declaration. And the
loss is per procedure: add a second, clean procedure to the file and it still
verifies, so the summary reads `All 1 goals passed.` while `m` is checked for
nothing at all. A healthy-looking run is therefore not evidence that every
procedure in the file was checked.

Past that the cause is upstream and untraced: the two blocks are well-scoped in
the source, so something between block flattening and VC generation drops the
procedure's obligations rather than renaming the shadowed declaration or
rejecting it. Worth reporting with the repro above.

**Contained, on RelRL's side.** A bicommand emits its statements into one flat
block, so `if`s from two different bicommands become siblings and a repeated
name reaches this directly. `refuse_declarations` in
`Translate/Bicommands.lean` refuses *any* Core declaration inside a `|- … -|`
or a split's side, nested ones included, which removes RelRL's route to it:

```console
$ relrl verify sides.relrl.st
sides.relrl.st(5, (5-44)) `y` cannot be declared inside a split's side: `Var` is
the only form that declares. Write `Var y : … | … ;` before the bicommand.
Finished with 0 goals checked, but 1 error(s) occurred.   # exit 1
```

That refusal is not only containment — `Var` being the only binder is WhyRel's
own rule, whose `|_ … _|` takes an `atomic_command` and whose only binder is
`Var … in CC`. But it is what keeps the defect unreachable, so widen it, never
loosen it, until the upstream fix lands. A `Var` cannot reach the defect: its
declarations are top-level in the composed block, where a repeat is already
reported as a collision against its own source range.

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
