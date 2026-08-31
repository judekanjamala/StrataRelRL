# toCore

> **Scope.** `relrl toCore` only — its output and what the lowering makes
> visible. Translation stages are in [`pipeline.md`](pipeline.md).

```console
relrl toCore <file.relrl.st> [--include <dir>]...
```

Translate to Core and print the result as Core concrete syntax on stdout. No
solver is involved. This is [`verify`](verify.md) stopped one stage early, and it
exists so translation and verification stay decoupled: the output is an ordinary
`.core.st` file for any generic Core tool.

Defined at `to_core_command` in `RelRL/Cli/ToCore.lean`. Mirrors how the upstream
`laurelToCore` command splits Laurel.

## Stages

1. Parse to `StrataDDM.Program` ([`pipeline.md`](pipeline.md) §1).
2. `translate_program` — self-composition lowering ([`pipeline.md`](pipeline.md)
   §2). Identical to what `verify` runs.
3. `coreToStrataProgram` + `StrataDDM.Program.toString` — print via DDM's
   formatter, driven by the same `#dialect` declaration that parses Core.

## Output

```console
$ relrl toCore RelRL/Examples/SeqBi.relrl.st
program Core;
procedure aligned ()
{
  biproc: {
    var a : int;
    var |a'| : int;
    a := 0;
    |a'| := 0;
    var b : int;
    var |b'| : int;
    b := 0;
    |b'| := 0;
    a := 1;
    |a'| := 1;
    assert [assert_1_1]: a == a';
    assert [assert_1_2]: b == 0 && b' == 0;
    b := 2;
    |b'| := 2;
    assert [assert_2_1]: a == a';
    assert [assert_2_2]: b == b';
  }
};
```

Everything the lowering does is visible here:

- The `biproc` became a Core `procedure` **of the same name**.
- Both sides are in one flat statement list inside a single block labelled
  `biproc`, with no `left:`/`right:` nesting. They interleave **per bicommand** —
  each element's left statements, then its right ones — so the two declarations
  pair up, then the two `a := 1` steps, then the `Assert` that relates them.
  Not left-in-full followed by right-in-full; `docs/design.md` says why the
  difference matters.
- Each `Var a : int | a : int ;` became **two** declarations, `a` and `a'` —
  the pair a bi-local is. Each `|- … -| ;` had its one statement emitted twice,
  unprimed then primed, which is the `a := 0` / `|a'| := 0` beneath it.
- The right side's statements are primed: `a` → `a'`, `b` → `b'`. The left side
  is never touched.
- Each `Assert { R }` became Core `assert`s where it stands. Its top-level
  `/\` was split, so `Agree a /\ Agree b` is two obligations rather than one —
  labelled `assert_2_1`, `assert_2_2`, since a relational formula carries no
  label of its own. A `requires`/`ensures` would instead appear in a Core
  `spec { … }` above the body; `Params.relrl.st` shows that.

## A printing quirk

Primed names print two ways in the same output: `var |a'|` in declarations and
assignment targets, but bare `a'` inside the asserts.

The asserts are built directly as Core expressions by the translator
(`lower_rformula` constructs the `Core.Expression.Expr`), while the
declarations went through Core's own `renameLhs` and print through the binding
printer, which pipe-escapes the `'`. Both spellings denote the same name —
`'` is a valid identifier character in DDM's tokenizer, and `|a'|` is the
pipe-delimited escape for the same string — so the output re-parses either way.
It is cosmetic, but worth knowing before you diff two `toCore` outputs by eye.

## Exit codes

| Code | Meaning | Trigger |
|---|---|---|
| 0 | printed | including when translation emitted a non-fatal diagnostic |
| 1 | user error | parse error, unreadable file, bad flag, or an error in the source program |
| 3 | `internalError` | a broken translator invariant |

**The output still prints on a fatal diagnostic, but the exit code fails.**
Printing is the point of the command, so the Core program goes to stdout either
way; a fatal diagnostic means it is not the program written, and exiting 0 would
hand a silently-wrong `.core.st` file to whatever consumes it next. A non-fatal
diagnostic still prints to stderr and still exits 0, so check stderr as well if
you script around it.

## Intended use

Save the output and hand it to a generic Core tool:

```console
$ relrl toCore RelRL/Examples/Swap.relrl.st > swap.core.st
$ strata verify swap.core.st
```

That second step is what the command's help text points at; it needs the
separate `strata` binary, which this repo does not build (see `docs/design.md`
on why RelRL ships its own CLI instead).
