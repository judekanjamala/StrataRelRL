# RelRL end-to-end workflow

Last verified end-to-end: 2026-08-20 (`lake build relrl`, then
`relrl relrlVerify RelRL/Examples/Swap.relrl.st` → 4/4 goals passed).

## 1. The user writes a concrete RelRL program

`RelRL/DDMTransform/Grammar.lean` declares the dialect with `#dialect … #end`:

A program file looks like `RelRL/Examples/Swap.relrl.st`:

```
program RelRL;

( {
    var a : int := 0;
    var b : int := 0;
    a := 3;
    b := 3;
    assert [left_a_then_b]: a == 3;
    assert [left_a_then_b]: b == 3;
  }; | {
    var a : int := 0;
    var b : int := 0;
    b := 3;
    a := 3;
    assert [right_b_then_a]: a == 3;
    assert [right_b_then_a]: b == 3;
  };
)
```

Parsing this file (`StrataDDM.readStrataText`) produces a generic
`StrataDDM.Program` — dialect-agnostic DDM AST, every node carrying its
`SourceRange` and dialect-declared metadata (e.g. the `[left_a_then_b]`
label).

## 2. `StrataDDM.Program` → `Core.Program` (`RelRL.DDMTransform.Translate`)

`RelRL/DDMTransform/Translate.lean` is the dialect-owned translator. It
hand-walks the raw `Operation`/`Arg` AST directly rather than going through
the generated `ofAst` Lean AST (see *Design decisions* below):

- `translateProgram` walks each top-level `Operation` in `p.commands`. An
  `RelRL.command_bicommand`-wrapped `RelRL.biembed` is lowered by
  `lowerBicommand` and wrapped in a nameless Core procedure; everything
  else is ordinary embedded Core syntax, delegated straight to Core's own
  `Core.getProgram`.
- `lowerBicommand` lowers `biembed left right` to a single Core
  `Statement.block "biembed" [leftStmt, rightStmt] md`: a `left:` block
  followed by a `right:` block, as one sequential Core block.
- `lowerCommandOp` recurses through nested `RelRL.command_bicommand`s (for
  future relational operators) and, for ordinary Core commands, delegates
  to `translateCoreOp`, which wraps the single `Operation` in a synthetic
  singleton `StrataDDM.Program` and calls `Core.getProgram`.
  `extractSideStatements` then unwraps the nameless procedure Core produces
  for a bare block back into a plain statement list.
- Translation runs in `TranslateM` (a `StateM` over an `Array Message`), so
  malformed bicommands produce diagnostics rather than panics.
- Source positions are preserved via `Imperative.MetaData.ofSourceRange`,
  so verifier diagnostics trace back to the original RelRL source span.

The result is an ordinary `Core.Program` — from here on RelRL is invisible;
everything downstream is exactly Core's pipeline, unmodified.

## 3. Core verification (`RelRL.Verify`)

`RelRL/Verify.lean` wraps `Strata.Core.verifyProgram` exactly the way Core's
own CLI commands do:

```
def verify (p : StrataDDM.Program) (ictx : Lean.Parser.InputContext := ..)
    (options : _root_.Core.VerifyOptions := .default) :
    IO (_root_.Core.VCResults × Array Message)
```

Internally: `translateProgram` (step 2) produces `(Core.Program,
translation diagnostics)`, then `Strata.Core.verifyProgram` runs Core's
existing VC-generation and SMT-discharge pipeline unmodified.
`verifyToMessages` is a convenience wrapper that formats both the
translation diagnostics and one `Message` per proof obligation.

Naming gotcha, documented in the file: bare `Core` is ambiguous inside this
package, because `Strata.Core` also names the generated `StrataDDM.Dialect`
value for the Core dialect and shadows the `Core` *namespace*. Hence the
`_root_.Core.` prefixes on `VerifyOptions`, `VCResult`, etc.

## 4. Driving it: the standalone `relrl` CLI

`Main.lean` + `RelRL/Cli.lean` define a self-contained `lean_exe` built on the
shared `Strata.Cli.Framework` from the `Strata` dependency, so no
`Strata-CLI` checkout is involved.

`buildRelRLDialectFileMap` preloads the `Core` and `RelRL` dialects (plus the
DDM builtins) into the `DialectFileMap`, so `.relrl.st` files parse without
any `--include` search path; `--include` is still accepted for extra
dialects. `relrlVerify` accepts the same
`--check-mode`/`--solver`/`--vc-directory`/etc. flags as the generic
`strata verify` command (`Strata.Cli.VerifyOptions`), and uses the same
exit-code scheme (0 = success, 2 = failures found, 3 = internal error).

`relrlToCore` stops after step 2 and prints the translated program, which is
ordinary Core concrete syntax — save it as a `.core.st` file and verify it
with any generic Core tool. For `Swap.relrl.st` the output is:

```console
$ ./.lake/build/bin/relrl relrlToCore RelRL/Examples/Swap.relrl.st
program Core;
procedure || ()
{
  biembed: {
    left: {
      var a : int := 0;
      var b : int := 0;
      a := 3;
      b := 3;
      assert [left_a_then_b]: a == 3;
      assert [left_a_then_b]: b == 3;
    }
    right: {
      var a : int := 0;
      var b : int := 0;
      b := 3;
      a := 3;
      assert [right_b_then_a]: a == 3;
      assert [right_b_then_a]: b == 3;
    }
  }
};
```

That decoupling mirrors how `laurelToCore` separates Laurel translation
from Core verification.

## Design decisions

Recorded here because they were settled during development and are not
recoverable from the code alone:

- **Translate to Core, not to Imperative + Lambda.** All Strata analysis and
  verification runs on the internal Lambda/Imperative ASTs, but Core is the
  supported entry point that already wires up VC generation and SMT
  discharge. A new dialect should lower to `Core.Program` and inherit that
  pipeline rather than hooking up a verifier itself.
- **Hand-walk the DDM AST; don't use `ofAst`.** `#strata_gen` produces a
  typed Lean AST and an `ofAst` conversion (exercised by
  `RelRL/Examples/Sample.lean`), but no dialect in Strata actually translates
  through it — Core, C_Simp, and Laurel all walk `Operation`/`Arg` by hand.
  Following that practice is what makes reusing `Core.getProgram` possible
  instead of re-implementing per-statement translation.
- **Own package, own CLI.** The repo split follows Strata's
  `docs/verso/IRTranslationPhilosophyDoc.lean` ("Relation to the proposed
  repository split", issue #1168): a dialect plus its translation-to-Core
  depends on `Strata`, never the reverse. The self-contained `lean_exe relrl`
  extends that to tooling — wiring RelRL into `Strata-CLI` was attempted
  first and abandoned after it spread the `Strata.Core`/`Core` namespace
  ambiguity into another repo's build.
