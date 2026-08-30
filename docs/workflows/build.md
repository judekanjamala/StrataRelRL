# Build

> **Scope.** Building the library and the `relrl` binary, and what is
> compiled-in rather than read at run time. See [`README.md`](README.md) for the
> other workflows.

```console
lake build relrl          # library + `relrl` binary
lake exe relrl <cmd> …    # resolves and rebuilds, then runs
```

`lake exe` rebuilds before running, so it is the right entry point during
development; `./.lake/build/bin/relrl` runs whatever was built last.

## What the build actually does

The step that distinguishes this project from an ordinary Lean library is
`RelRL/DDMTransform/Grammar.lean`. `#dialect … #end` is a Lean *elaborator*: it
runs at `lake build` time and emits an ordinary compiled constant,
`Strata.RelRL : StrataDDM.Dialect`, into that module's `.olean`.

So the grammar is a build product, not a file read at run time. Three
consequences:

- **A grammar edit is a compile error, not a run-time error.** Ill-formed
  syntax in the dialect fails `lake build`, with the message pointing into
  `Grammar.lean`.
- **`relrl verify` never opens `Grammar.lean`,** nor any `.dialect.st` file.
  Traced with `strace -f -e trace=openat`, the only files a verify run opens —
  shared libraries and `/etc`, `/proc` aside — are the `.relrl.st` input,
  `/dev/urandom`, and the SMT scratch file under `/tmp`.
- **A `#strata … #end` block in a Lean file is a real grammar test.** It
  exercises the same compiled `Dialect`, at the moment it is produced.

This is also where the namespace shadowing documented in `RelRL/Verify.lean`
comes from: `Strata.Core` names both a `Dialect` *value* and the namespace
holding `Core.Program`, which is why the CLI writes `_root_.Core.VerifyOptions`.

## How the dialect reaches the parser

The compiled constant is statically linked into `relrl`, and
`build_relrl_dialect_file_map` (`RelRL/Cli.lean`) hands it to the parser as
data:

```lean
let preloaded := StrataDDM.Elab.LoadedDialects.builtin
  |>.addDialect! Strata.Core
  |>.addDialect! Strata.RelRL
```

Dialect *selection* then happens per input file: the `program RelRL;` header
names the dialect, which is looked up by name in the preloaded
`LoadedDialects`. A miss falls through to the `DialectFileMap`, which is empty
unless `--include` was passed — rename the header to an unknown dialect and the
run fails with `Exception: Unknown dialect …`.

`--include <dir>` is the one path that loads a dialect at run time: it scans the
directory for `.dialect.st` / `.dialect.st.ion` files and registers them in the
`DialectFileMap` for lazy loading on first reference
(`StrataDDM/Elab/LoadedDialects.lean`, `DialectFileMap.add`). RelRL never needs
it, since its own dialect is compiled in and so is always found first.

## Targets

`lakefile.toml` declares:

| Target | Kind | Contents |
|---|---|---|
| `RelRL` | `lean_lib` | `RelRL`, `RelRL.DDMTransform.+`, `RelRL.Verify`, `RelRL.Cli` — the default target |
| `RelRLExamples` | `lean_lib` | globs `RelRL.Examples.+` |
| `relrl` | `lean_exe` | root `Main`, the standalone CLI |

`RelRL/Examples/` currently holds only `.relrl.st` files, so the
`RelRLExamples` glob matches no Lean modules and the target builds empty.

## Things that will bite

- **`warningAsError = true`.** An unused variable or a shake warning fails the
  build, not just warns.

- **The `Strata` dependency is unpinned** — `rev = "main"` in `lakefile.toml`. A
  build that breaks after `lake update` may be upstream drift rather than a
  local change. Check `git diff` before assuming it is your edit.

- **Inside `#dialect … #end`, comments are `//`, not `--`.** A `--` comment
  yields `expected token` at that line with no hint about why: DDM's tokenizer
  only treats `/`-initiated sequences as comments, so `--` tokenizes as ordinary
  symbols.

## Not covered

There is no test target. `RelRLTest/` was removed; the smoke test is running
`relrl verify` over `RelRL/Examples/` and checking the goal counts — see
[`verify.md`](verify.md).
