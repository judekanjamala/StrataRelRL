# project

> **Scope.** `relrl project` only — what projection keeps, drops and prints.
> Translation stages are in [`pipeline.md`](pipeline.md).

```console
relrl project <file.relrl.st> --side left|right [--include <dir>]...
```

Print the Core concrete syntax of **one side** of every `biproc` — the unary
program that side denotes on its own, with neither the other side nor the
relational `ensures`. No solver is involved.

Defined at `project_command` in `RelRL/Cli/Project.lean`, over the `.project side` case
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
$ relrl project RelRL/Examples/SeqBi.relrl.st --side left
program Core;
procedure aligned ()
{
  left: {
    var a : int;
    a := 0;
    var b : int;
    b := 0;
    a := 1;
    b := 2;
  }
};
```

```console
$ relrl project RelRL/Examples/SeqBi.relrl.st --side right
program Core;
procedure aligned ()
{
  right: {
    var a : int;
    a := 0;
    var b : int;
    b := 0;
    a := 1;
    b := 2;
  }
};
```

Note the contrast with [`toCore`](toCore.md) on the same file: there the block
is labelled `biproc` and holds both sides with the right one primed; here the
block is labelled with the side, and `a`/`b` are unprimed in *both* projections.
The `Assert` between the two aligned steps is gone as well — it names both
sides, and a projection has only one.

The synchronized `|- … -|` that declares `a` and `b` appears in both projections,
since it is a command both programs run.

## Exit codes

| Code | Meaning | Trigger |
|---|---|---|
| 0 | printed | |
| 1 | user error | missing or unrecognised `--side`, parse error, unreadable file, or an error in the source program |
| 3 | `internalError` | a broken translator invariant — the program printed is not the program written |

One source error reaches projection: a `datatype`, or a `rec` block of more than
one function, in a file that also declares a `biproc`. That guard is not
mode-gated, because what it protects — the top-level binding list every body is
lowered against — is as wrong here as under `verify`
([`issues.md`](../issues.md)). No body is lowered once it fires, so what prints
is the Core declarations alone, and the exit code is 1.

The duplicate-declaration check does *not* run here: it is about names colliding
in the one block self-composition fuses, and a projection has no such block.

The exit-3 row is defensive: the remaining translation diagnostics come from
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
