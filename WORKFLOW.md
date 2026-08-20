# RRL end-to-end workflow: concrete syntax in, verification errors out

How a `.rrl.st` file becomes verification diagnostics, stage by stage, and
why the pipeline is built this way. For what RRL is, what currently works,
and how to build and run it, see `README.md`.

Last verified end-to-end: 2026-08-20 (`lake build rrl`, then
`rrl rrlVerify RRL/Examples/Swap.rrl.st` → 4/4 goals passed).

## 1. The user writes a concrete RRL program

`RRL/DDMTransform/Grammar.lean` declares the dialect with `#dialect … #end`:

```
dialect RRL;
import Core;

category Bicommand;
op biembed (left : Command, right : Command) : Bicommand => "(" left " | " right ")";
op command_bicommand (b : Bicommand) : Command => b;
```

`import Core` means each side of a bicommand is parsed by Core's own rules,
and `command_bicommand` injects `Bicommand` back into Core's `Command`
category so a bicommand may appear anywhere a Core command may. DDM derives
the concrete parser and pretty-printer from this declaration alone.

A program file looks like `RRL/Examples/Swap.rrl.st`:

```
program RRL;

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

Note the trailing `;` after each `{ ... }` side (each side is a full Core
`Command`, i.e. `command_block`, whose own grammar rule is `b ";\n"`), and
*no* trailing `;` after the closing `)` (`command_bicommand`'s rule is
just `b`, with no separator of its own).

Parsing this file (`StrataDDM.readStrataText`) produces a generic
`StrataDDM.Program` — dialect-agnostic DDM AST, every node carrying its
`SourceRange` and dialect-declared metadata (e.g. the `[left_a_then_b]`
label).

## 2. `StrataDDM.Program` → `Core.Program` (`RRL.DDMTransform.Translate`)

`RRL/DDMTransform/Translate.lean` is the dialect-owned translator. It
hand-walks the raw `Operation`/`Arg` AST directly rather than going through
the generated `ofAst` Lean AST (see *Design decisions* below):

- `translateProgram` walks each top-level `Operation` in `p.commands`. An
  `RRL.command_bicommand`-wrapped `RRL.biembed` is lowered by
  `lowerBicommand` and wrapped in a nameless Core procedure; everything
  else is ordinary embedded Core syntax, delegated straight to Core's own
  `Core.getProgram`.
- `lowerBicommand` lowers `biembed left right` to a single Core
  `Statement.block "biembed" [leftStmt, rightStmt] md`: a `left:` block
  followed by a `right:` block, as one sequential Core block.
- `lowerCommandOp` recurses through nested `RRL.command_bicommand`s (for
  future relational operators) and, for ordinary Core commands, delegates
  to `translateCoreOp`, which wraps the single `Operation` in a synthetic
  singleton `StrataDDM.Program` and calls `Core.getProgram`.
  `extractSideStatements` then unwraps the nameless procedure Core produces
  for a bare block back into a plain statement list.
- Translation runs in `TranslateM` (a `StateM` over an `Array Message`), so
  malformed bicommands produce diagnostics rather than panics.
- Source positions are preserved via `Imperative.MetaData.ofSourceRange`,
  so verifier diagnostics trace back to the original RRL source span.

The result is an ordinary `Core.Program` — from here on RRL is invisible;
everything downstream is exactly Core's pipeline, unmodified.

## 3. Core verification (`RRL.Verify`)

`RRL/Verify.lean` wraps `Strata.Core.verifyProgram` exactly the way Core's
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

## 4. Driving it: the standalone `rrl` CLI

`Main.lean` + `RRL/Cli.lean` define a self-contained `lean_exe` built on the
shared `Strata.Cli.Framework` from the `Strata` dependency, so no
`Strata-CLI` checkout is involved.

`buildRRLDialectFileMap` preloads the `Core` and `RRL` dialects (plus the
DDM builtins) into the `DialectFileMap`, so `.rrl.st` files parse without
any `--include` search path; `--include` is still accepted for extra
dialects. `rrlVerify` accepts the same
`--check-mode`/`--solver`/`--vc-directory`/etc. flags as the generic
`strata verify` command (`Strata.Cli.VerifyOptions`), and uses the same
exit-code scheme (0 = success, 2 = failures found, 3 = internal error).

`rrlToCore` stops after step 2 and prints the translated program, which is
ordinary Core concrete syntax — save it as a `.core.st` file and verify it
with any generic Core tool. For `Swap.rrl.st` the output is:

```console
$ ./.lake/build/bin/rrl rrlToCore RRL/Examples/Swap.rrl.st
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
  `RRL/Examples/Sample.lean`), but no dialect in Strata actually translates
  through it — Core, C_Simp, and Laurel all walk `Operation`/`Arg` by hand.
  Following that practice is what makes reusing `Core.getProgram` possible
  instead of re-implementing per-statement translation.
- **Left and right are separate state spaces.** The same variable name on
  both sides denotes different state; the lowering introduces no shared
  heap and never aliases them.
- **`biembed`, not `bisplit`.** The operator was renamed early; the leftover
  `RRL/Examples/Bisplit.lean` is a duplicate of `Sample.lean` from before
  that rename.
- **Own package, own CLI.** The repo split follows Strata's
  `docs/verso/IRTranslationPhilosophyDoc.lean` ("Relation to the proposed
  repository split", issue #1168): a dialect plus its translation-to-Core
  depends on `Strata`, never the reverse. The self-contained `lean_exe rrl`
  extends that to tooling — wiring RRL into `Strata-CLI` was attempted
  first and abandoned after it spread the `Strata.Core`/`Core` namespace
  ambiguity into another repo's build.
