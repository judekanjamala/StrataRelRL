# Known issues

## CLI help and error messages name `strata`, not `relrl`

`relrl --help`, `relrl <cmd> --help`, and the CLI error paths all print
`strata` as the program name:

```console
$ relrl --help
Usage: strata <command> [flags]...

Command-line utilities for working with Strata.
...
$ relrl bogus
Exception: Expected subcommand, got bogus.

Run strata --help for additional help.
```

The name is hardcoded in the shared `Strata.Cli.Framework` from the `Strata`
dependency, in four places: `printGlobalHelp` (the usage line and tagline),
`printCommandHelp` (the usage line), and the default hints of `exitFailure`
and `exitCmdFailure`. The framework takes no program-name parameter.

Only cosmetic — dispatch, flags, and exit codes are all correct.

Two possible fixes, neither taken:

1. **Upstream.** Add a program name to `CommandGroup`, or a `progName`
   parameter threaded through the help printers and exit helpers. The right
   fix, since every non-`strata` binary built on the framework has this bug.
2. **Local override.** Reimplement `printGlobalHelp`/`printCommandHelp` in
   `Main.lean` and dispatch `--help` before delegating to `runCommandMap`.
   This works but is partial: `printIndented` and `printFlag` are `private`
   in the framework and would have to be duplicated, and the two
   `exitCmdFailure` paths inside `parseArgs` (unknown flag, wrong argument
   count) stay wrong unless `parseArgs` is forked too — which would put our
   flag-parsing semantics at risk of drifting from upstream's.

## `translateCoreOp` assumes every non-`birelate` command is Core

`RelRL/DDMTransform/Translate.lean` builds its singleton program with a
hardcoded dialect map:

```lean
let singleton := StrataDDM.Program.create Core_map "Core" #[op]
```

`Core_map` contains Core, `Init`, and Core's imports — not `RelRL`. This is
sound today only by accident of the grammar: RelRL declares exactly two
operators, `birelate` (which `translateProgram` filters out before reaching
here) and `biembed` (which is unreachable at a program's top level, since
`Bicommand` appears only as `birelate`'s `body`). So nothing but a Core
operation ever arrives.

It stops being sound the moment RelRL gains a second top-level operator, or
imports a second dialect. A non-Core operation would then be handed to
`Program.create` with a map that does not contain its dialect.

The fix is to thread the real dialect map — the one the CLI already builds in
`buildRelRLDialectFileMap` — through `translateProgram` into `translateCoreOp`,
rather than referring to `Core_map` by name. Deferred until there is a second
operator to motivate it.

## Relational specs relate variables only, not expressions

`ensures [l]: left_a == right_a` takes two *identifiers*, not two expressions.
`RelRL/DDMTransform/Grammar.lean` declares `rel_agree`'s operands as `Ident`, so
`left_a == right_a + 1` does not parse.

This is forced by the phase structure rather than chosen. DDM resolves names
during elaboration, and elaboration finishes before translation begins. The
names a relational spec refers to — `left_a`, `right_a` — are *created* by
translation's renaming pass, so they cannot be resolved as expressions:
elaborating `e : bool` against them fails with `Unknown expr identifier left_a`.
`Ident` is lexical and needs no resolution, which is why it works.

Widening this needs one of:

1. A DDM mechanism to declare synthesized names into an argument's scope.
   `@[declare(v, tp)]` binds the name held by argument `v`; there is no way to
   declare a name *derived* from one.
2. Doing the renaming before elaboration rather than after — that is, rewriting
   the DDM `Operation` tree instead of the Core AST. Possible, but it means
   identifying variable references in a generic tagged tree without Core's
   type information.
3. Keeping the sides' variable names distinct in the source, so no renaming is
   needed and the spec can be an ordinary `bool` scoped over both sides. This
   still needs the sides' locals to escape their blocks, which Core `Block`
   deliberately prevents.
