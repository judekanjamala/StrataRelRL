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

## `translate_core_op` assumes every non-`biproc` command is Core

`RelRL/DDMTransform/Translate.lean` builds its singleton program with a
hardcoded dialect map:

```lean
let singleton := StrataDDM.Program.create Core_map "Core" #[op]
```

`Core_map` holds Core, `Init` and Core's imports — not `RelRL`. Sound today
only by accident of the grammar: `biproc` is filtered out before reaching here,
and `biembed` is unreachable at top level, so only Core operations arrive. That
breaks the moment RelRL gains a second top-level operator or imports a second
dialect.

Fix: thread the real dialect map — the one `build_relrl_dialect_file_map`
already builds — through `translate_program` into `translate_core_op`, instead
of naming `Core_map`. Deferred until a second operator motivates it.

## Relational specs relate variables only, not expressions

`ensures [l]: a == a'` takes two *identifiers*, not two expressions.
`RelRL/DDMTransform/Grammar.lean` declares `rel_agree`'s operands as `Ident`, so
`a == a' + 1` does not parse.

Forced by the phase structure, not chosen. DDM resolves names during
elaboration, which finishes before translation begins — and `a'` is *created* by
translation's renaming pass, so an `e : bool` operand fails with `Unknown expr
identifier a'`. `Ident` is lexical and needs no resolution.

Widening it needs one of:

1. A DDM way to declare synthesized names into an argument's scope.
   `@[declare(v, tp)]` binds the name argument `v` holds; nothing declares a
   name *derived* from one.
2. Renaming before elaboration — rewriting the DDM `Operation` tree instead of
   the Core AST. Means spotting variable references in a generic tagged tree
   without Core's type information.
3. Distinct variable names per side in the source, so no renaming is needed.
   Still requires the sides' locals to escape their blocks, which Core `Block`
   prevents by design.
