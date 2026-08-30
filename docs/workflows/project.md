# project

> **Scope.** `relrl project` only — what projection keeps, drops and prints.
> Translation stages are in [`pipeline.md`](pipeline.md).

```console
relrl project <file.relrl.st> --side left|right [--include <dir>]...
```

Print the Core concrete syntax of **one side** of every `biproc` — the unary
program that side denotes on its own, with neither the other side nor the
relational `ensures`. No solver is involved.

Defined at `project_command` in `RelRL/Cli.lean`, over the `.project side` case
of `translate_program_with`.

## Why it exists

A relational judgement is a statement about two programs. `verify` checks it by
fusing them into one; `project` recovers the two programs being talked about. It
is the answer to "what exactly is the left-hand program here?" — useful when a
spec fails and you need to know whether the fault is in one side or in the
relation between them.

## What projection drops

Everything that exists only because the two sides share a scope:

- **The other side.** `lower_bicommand` keeps this side's statements from every
  bicommand, in order, and nothing of the other. A synchronized `|- … -|` runs
  on both sides, so it is kept whole and emitted once.
- **Priming.** Nothing is renamed, on either side. Priming keeps the sides apart
  inside one procedure; with one side alone there is nobody to collide with, so
  the right projection keeps its source names too.
- **The `ensures` clause, and every `Assert { R }`.** A relational formula names
  both sides, so it says nothing about one side alone. They are dropped rather
  than lowered.

What remains is an ordinary unary `Core.Program`: one procedure per `biproc`,
under the `biproc`'s own name.

## Output

```console
$ relrl project RelRL/Examples/Swap.relrl.st --side left
program Core;
procedure swap ()
{
  left: {
    var a : int := 0;
    var b : int := 0;
    a := 3;
    b := 3;
  }
};
```

```console
$ relrl project RelRL/Examples/Swap.relrl.st --side right
program Core;
procedure swap ()
{
  right: {
    var a : int := 0;
    var b : int := 0;
    b := 3;
    a := 3;
  }
};
```

Note the contrast with [`toCore`](toCore.md) on the same file: there the block
is labelled `biproc` and holds both sides with the right one primed; here the
block is labelled with the side, and `a`/`b` are unprimed in *both* projections.

The synchronized `|- … -|` that declares `a` and `b` appears in both projections,
since it is a command both programs run.

## Exit codes

| Code | Meaning | Trigger |
|---|---|---|
| 0 | printed | |
| 1 | user error | missing or unrecognised `--side`, parse error, unreadable file |
| 3 | `internalError` | translation emitted a diagnostic — the program printed is not the program written |

The exit-3 row is defensive: translation diagnostics come from
`emit_invariant_violation`, which fires only if the grammar and translator have
drifted, so no `.relrl.st` input reaches it. A relational formula that Core
later rejects does *not* trigger it here — projection drops formulas before they
are lowered, so `project` exits 0 on a file `verify` exits 3 on.

`--side` is required and accepts exactly `left` or `right` (`Side.of_string?`):

```console
$ relrl project RelRL/Examples/Swap.relrl.st
Exception: project requires --side left or --side right.

$ relrl project RelRL/Examples/Swap.relrl.st --side middle
Exception: Unknown side 'middle': expected left or right.
```

## Intended use

Save a projection as a `.core.st` file and verify that side on its own with a
generic Core tool, exactly as with [`toCore`](toCore.md). Between the two
projections and the self-composition, you have all three programs a relational
proof involves.
