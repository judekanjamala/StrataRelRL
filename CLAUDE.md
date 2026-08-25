# StrataRelRL

A Strata dialect adding **bicommands** on top of Strata Core, verified by
lowering to Core. `README.md` covers intent, current state, and the file layout;
`docs/workflow.md` the pipeline; `docs/design.md` the decisions and why they went
that way; `docs/issues.md` known defects.

## Commands

```console
lake build relrl
lake exe relrl verify RelRL/Examples/Swap.relrl.st   # smoke test: expect 4/4 goals passed
lake exe relrl toCore RelRL/Examples/Swap.relrl.st   # print the translated Core program
```

`lake exe` resolves and rebuilds; prefer it over `./.lake/build/bin/relrl`.
Verification needs an SMT solver on `PATH` (cvc5 by default).

## Things that will bite

- **The `Strata` dependency is unpinned** — `rev = "main"` in `lakefile.toml`.
  A build that breaks after `lake update` may be upstream drift rather than a
  local change. Check `git diff` before assuming it's your edit.

- **`warningAsError = true`.** An unused variable or a shake warning fails the
  build, not just warns.

- **Two `Core` namespaces.** `Strata.Core` (the dialect) and `_root_.Core` (the
  verification IR) both exist and resolve differently depending on the enclosing
  namespace. `RelRL/Cli.lean` writes `_root_.Core.VerifyOptions`,
  `_root_.Core.VCResult` for exactly this reason. Wiring RelRL into `Strata-CLI`
  was abandoned over this; see `docs/design.md`.

- **Inside `#dialect … #end`, comments are `//`, not `--`.** A `--` comment
  yields `expected token` at that line with no hint about why.

## The invariant worth protecting

In `RelRL/DDMTransform/Grammar.lean`, `biembed`'s two sides are Core `Block`,
**not** `Command`, and `Bicommand` is not a `Command`:

```
op birelate (name : Ident, body : Bicommand) : Command => "birelate " name " = " body ";";
op biembed  (left : Block, right : Block) : Bicommand  => "(" left " | " right ")";
```

This is what makes bicommand nesting structurally impossible: no Core
`Statement`/`Block` operator takes a `Command`, so a `Bicommand` cannot recur
through its own sides. Making the sides `Command`, or adding
`op inj (b : Bicommand) : Command => b`, reintroduces nesting immediately —
`( ( a | b ) | c )` starts parsing. `docs/design.md` has the full argument.

## Reading the dependency

Vendored sources are the reference, and they are worth reading directly rather
than guessing at:

| Path under `.lake/packages/` | What's there |
|---|---|
| `Strata/Strata/Languages/Core/DDMTransform/Grammar.lean` | Core's dialect — the categories and ops RelRL builds on |
| `Strata/Strata/Cli/Framework.lean` | flag parsing, exit codes, help printing |
| `StrataDDM/StrataDDM/BuiltinDialects/` | `Init`, `StrataDDL`, `StrataHeader` |
| `StrataDDM/StrataDDM/Elab/Core.lean` | the elaborator: scoping, typechecking, `elabCommand` |
