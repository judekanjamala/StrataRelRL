# RelRL end-to-end workflow

Last verified end-to-end: 2026-08-21 (`lake build relrl`, then
`relrl verify RelRL/Examples/Swap.relrl.st` → 4/4 goals passed),
against `Strata` upstream `main`.

## 1. Concrete RelRL program to `StrataDDM.Program`

`RelRL/DDMTransform/Grammar.lean` declares the dialect with `#dialect … #end`. 

`buildRelRLDialectFileMap` preloads the `Core` and `RelRL` dialect constants
(plus the DDM builtins) into the `DialectFileMap`, so `.relrl.st` files parse
without any `--include` search path; `--include` is still accepted for extra
dialects.

`StrataDDM.readStrataText` parses the program text. It is the inbuilt parser and
produces a generic `StrataDDM.Program` — dialect-agnostic DDM AST, every node
carrying its `SourceRange` and dialect-declared metadata (e.g. the
`[left_a_then_b]` label). 

### The grammar is compiled, not parsed at verify time

`#dialect … #end` is a Lean elaborator: it runs at `lake build` time and emits
an ordinary compiled constant, `Strata.RelRL : StrataDDM.Dialect`, into
`RelRL.DDMTransform.Grammar`'s `.olean`. (This is also where the namespace
shadowing documented in `RelRL/Verify.lean` comes from — `Strata.Core` names
both a `Dialect` *value* and the namespace holding `Core.Program`.)

That constant is statically linked into `relrl`, and `buildRelRLDialectFileMap`
hands it to the parser as data:

```lean
let preloaded := StrataDDM.Elab.LoadedDialects.builtin
  |>.addDialect! Strata.Core
  |>.addDialect! Strata.RelRL
```

So `relrl verify foo.relrl.st` never reads `Grammar.lean`, nor any
`.dialect.st` file. Traced with `strace -f -e trace=openat`, the only files a
verify run opens — shared libraries and `/etc`, `/proc` aside — are the
`.relrl.st` input, `/dev/urandom`, and the SMT scratch file under `/tmp`.

Dialect *selection* happens per input file: the `program RelRL;` header names
the dialect, which is looked up by name in the preloaded `LoadedDialects`. A
miss falls through to the `DialectFileMap`, which is empty unless `--include`
was passed — rename the header to an unknown dialect and the run fails with
`Exception: Unknown dialect …`.

`--include <dir>` is the one path that does load a dialect at runtime: it scans
the directory for `.dialect.st` / `.dialect.st.ion` files and registers them in
the `DialectFileMap` for lazy loading on first reference
(`StrataDDM/Elab/LoadedDialects.lean`, `DialectFileMap.add`). RelRL never takes
it, since its own dialect is compiled in and so is always found first.

Consequently the grammar is re-parsed only by `lake build`, after an edit to
`Grammar.lean` — which is what makes the `#strata` blocks in `RelRLTest/` valid
grammar tests: they exercise the same compiled `Dialect`, at the moment it is
produced.

## 2. `StrataDDM.Program` → `Core.Program` (`RelRL.DDMTransform.Translate`)

`RelRL/DDMTransform/Translate.lean` 

- `translateProgram` walks each top-level `Operation` in `p.commands`. A
  `RelRL.birelate` becomes a Core procedure *of the same name*, whose body is
  the lowered `biembed`; everything else is ordinary embedded Core syntax,
  delegated straight to Core's own `Core.getProgram`.
- `lowerBicommand` lowers `biembed left right` to one *flat* statement list:
  the left side's statements followed by the right side's, all inside a single
  `Statement.block "biembed" … md`.
- `lowerBlockArg` handles one side. The argument is a Core `Block`, so it is
  wrapped in a synthetic `Core.command_block` operation to become the
  top-level `Command` that `Core.getProgram` accepts, then passed to
  `translateCoreOp` (which wraps it in a singleton `StrataDDM.Program`).
  `unwrapBlockProcedure` then undoes that wrap, peeling off the nameless
  procedure Core produces to leave a plain statement list.
- `prefixSideVars` renames each side's top-level declarations to `left_<v>` /
  `right_<v>`, using Core's own `Block.substFvar` (reads) and
  `Block.renameLhs` (declaration and assignment targets).
- `lowerRelEnsures` turns the optional `ensures` clause into Core `assert`s
  appended after both sides.
- Translation runs in `TranslateM` (a `StateM` over an `Array Message`), so
  malformed bicommands produce diagnostics rather than panics.

### Why the sides are flattened rather than nested

The sides used to become `left:` and `right:` sub-blocks. They no longer do,
because a relational spec has to name both sides at once and a Core block's
locals are invisible once the block closes. Renaming makes the two sides
disjoint, so concatenating them is ordinary self-composition — the standard
encoding for the forall-forall fragment, and sound precisely because after
renaming neither side can observe the other.

Only *top-level* declarations of a side are renamed. One nested inside an `if`
or `while` body stays block-scoped, so it can neither collide across sides nor
be named by a spec.
- Source positions are preserved via `Imperative.MetaData.ofSourceRange`,
  so verifier diagnostics trace back to the original RelRL source span.

The result is an ordinary `Core.Program`. Everything downstream is exactly
Core's pipeline, unmodified.

## 3. Core verification (`RelRL.Verify`)


`RelRL/Verify.lean` wraps `Strata.Core.verifyProgram` exactly the way Core's
own CLI commands do:

```
def verify (p : StrataDDM.Program) (ictx : Lean.Parser.InputContext := ..)
    (options : _root_.Core.VerifyOptions := .default) :
    IO (_root_.Core.VCResults × Array Message)
```

`Strata.Core.verifyProgram` runs Core's
existing VC-generation and SMT-discharge pipeline unmodified.
`verifyToMessages` is a convenience wrapper that formats both the
translation diagnostics and one `Message` per proof obligation.

