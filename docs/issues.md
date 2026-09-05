# Known issues

> **Scope.** Defects in Strata or in this translation, each traced to its root
> cause and to what fixing it would take. Not a gap list: something RelRL simply
> does not implement yet, or a deliberate divergence from WhyRel, belongs in
> [`status.md`](status.md), which points here when the cause is a constraint
> that cannot be fixed.

## CLI help and error messages name `strata`, not `relrl`

```console
$ relrl --help
Usage: strata <command> [flags]...
$ relrl bogus
Exception: Expected subcommand, got bogus.

Run strata --help for additional help.
```

Hardcoded in `Strata.Cli.Framework` in four places: `printGlobalHelp` (usage line
and tagline), `printCommandHelp` (usage line), and the default hints of
`exitFailure` and `exitCmdFailure`. The framework takes no program-name
parameter. Cosmetic only — dispatch, flags and exit codes are correct. Where
`RelRL/Cli/Project.lean` passes an explicit hint the name is right, which is the
shape of the fix.

The right fix is upstream: thread a `progName` through the help printers and exit
helpers, since every non-`strata` binary on this framework has the bug. A local
override in `Main.lean` is partial — `printIndented` and `printFlag` are
`private`, and the two `exitCmdFailure` paths inside `parseArgs` stay wrong
unless `parseArgs` is forked, risking drift from upstream's flag semantics.

## A top-level declaration is shared by both programs

**Unsound against WhyRel's semantics.** WhyRel gives each side its own state, so
a global is two variables and the two programs may differ in it. Here a `const`
is one symbol both sides read, which makes agreement on anything derived from it
free:

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

`Agree r` should not be provable: nothing relates the two programs' `g`.

The cause is that a Core constant is a 0-ary *function*, so a reference lowers to
`.op "g"` and never `.fvar "g"`. Every priming helper is built on `substFvar`,
and every traversal in `Strata/DL/Lambda` passes `.op` through unchanged — there
is no substitution over operator names anywhere in Lambda or Core. Globals are
therefore invisible to priming, and to `fragment_names`, so `check_side` misses
them too.

Fixing it has two halves. **Duplicate the declarations**: a `const` or function
gets a primed copy; an `axiom` and a `distinct` get one with their references
primed, or `g'` is unconstrained while `g` is not; a `procedure` gets one, since
in WhyRel each side has its own. A `type` or `datatype` does not — a type is not
program state.

**Then rename references on the right**, by one of two routes:

- write an op-renaming traversal over `LExpr` and `Statement` — about thirty
  lines, and the first traversal of Core's AST this translator would own; or
- lower right-hand fragments against a *primed binding set*, so `translateExpr`
  emits `.op "g'"` directly. That needs `bi_sync` to lower its one statement
  twice, once per binding set, rather than once with a lexical rename after.

The first is contained and leaves the lexical-priming design intact; the second
avoids a new traversal but reworks how priming is applied.

## Sibling blocks sharing a declared name lose every obligation

Two Core blocks at the same level declaring the same name make Core's verifier
return **no obligations at all** for the enclosing procedure, silently and with
exit 0. This is Core's, not RelRL's — the repro has no bicommands in it:

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

Rename the second `y` and the `ensures` comes back as a checked obligation that
passes. Nothing is printed either way: the clause is not reported as failing,
unknown, or skipped — it is simply absent, so a passing run means nothing.

Two things narrow it. `--verbose` shows `Type checking succeeded.` and an empty
`VCs:` list, so the program is accepted and it is VC *generation* that emits
nothing. And the loss is per procedure: a second, clean procedure still verifies,
so the summary reads `All 1 goals passed.` while `m` is checked for nothing.

Past that the cause is upstream and untraced: the blocks are well-scoped in the
source, so something between block flattening and VC generation drops the
obligations rather than renaming or rejecting the shadowed declaration. Worth
reporting with the repro above.

**Contained, on RelRL's side.** A bicommand emits into one flat block, so `if`s
from two bicommands become siblings and a repeated name reaches this directly.
`refuse_declarations` in `Translate/Bicommands.lean` refuses *any* Core
declaration inside a `|- … -|` or a split's side, nested ones included:

```console
$ relrl verify sides.relrl.st
sides.relrl.st(5, (5-44)) `y` cannot be declared inside a split's side: `Var` is
the only form that declares. Write `Var y : … | … ;` before the bicommand.
Finished with 0 goals checked, but 1 error(s) occurred.   # exit 1
```

That refusal is WhyRel's own rule as well as containment — its `|_ … _|` takes an
`atomic_command`, and `Var … in CC` is its only binder. But it is what keeps the
defect unreachable, so widen it, never loosen it, until the upstream fix lands. A
`Var` cannot reach the defect: its declarations are top-level in the composed
block, where a repeat is already reported against its own source range.

## A `datatype` breaks the top-level binding list a `biproc` body resolves against

`translate_program_with` reconstructs Core's top-level binding list from the
decls `translateCoreDecls` returns:

```lean
let top : TransBindings := { freeVars := coreDecls.toArray }
```

That assumes one `freeVars` entry per returned decl. `translateCoreDecls` pushes
one decl per *command*, but two branches grow `freeVars` by more:

| Command | decls returned | `freeVars` entries added |
|---|---|---|
| `command_datatypes` | 1 | per datatype: the type, then every constructor, tester, field accessor and unsafe field accessor |
| `command_recfndefs` | 1 | one per function in the block |

Every other branch is 1:1. A `.fvar i` in a `biproc` body indexes DDM's global
context, so from the first such command onward `top.freeVars` is short and every
later index is off. An out-of-range index yields the default `Core.Decl`, which
lowers to the literal `0` — a reference to a top-level constant becomes `0`, and
a false spec can verify. Core's `translateExpr` also asserts `i <
bindings.freeVars.size`, so such a run prints a `PANIC` per misresolved
reference to **stderr**, where RelRL's CLI does not collect it.

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

No body is lowered once it fires, so Core's `assert!` is never reached. The guard
is exact, not conservative: a `datatype` in a file with no `biproc` still works —
that path goes through `translateCoreDecls` directly — as do a type synonym, an
opaque `type`, and a *single*-function `rec` block, all 1:1.

The fix is upstream: have `translateCoreDecls` return its final `TransBindings`
alongside the decls — it holds them at the end already — and have
`translate_program_with` use that as `top`. Correct for every command, present
and future, and the guard can then be deleted. The dependency is unpinned
(`rev = "main"`), so it is a patch upstream rather than a fork.

Do not fix it by reimplementing `translateCoreDecls`'s dispatch inside RelRL:
that duplicates a thirteen-case match against an unpinned dependency, which is
the drift CLAUDE.md warns about.

Nor by lowering a `biproc` into a Core `command_procedure` at the DDM level. That
is feasible but a rewrite of the translator, not a fix: a `|- c -|` holds *one*
fragment both programs run, so it must become two at different binder positions —
duplication with re-indexing, against a scope chain RelRL would maintain by hand,
with no `ExprF` index traversal upstream (`incIndices` is `TypeExprF`-only) and
references split between de Bruijn reads and lexical `lhsIdent` targets that must
agree. It also trades ~1100 lines of typed `Core.Statement` construction for
untyped `ArgF` arrays, where a shape error is a runtime failure. All to delete
this guard and one line, against the two-line upstream change above.
[`design.md`](design.md), "A `biproc` is lowered to Core terms".
