# StrataRelRL

An experimental [Strata](https://github.com/strata-org/Strata) dialect that
adds **bicommands** — paired left/right program fragments — on top of Strata
Core, and verifies them by lowering to Core and reusing Core's existing
SMT-backed verification pipeline unchanged.

The dialect is called `RRL`, after *relational region logic*. It ports ideas
from **WhyRel/RelRL** — the original OCaml implementation lives at
[dnaumann/RelRL](https://github.com/dnaumann/RelRL) — from Why3 onto Strata,
starting with the forall-forall (2-safety) fragment described in
[Nagasamudram et al., TACAS 2023](https://link.springer.com/chapter/10.1007/978-3-031-30820-8_11);
the underlying relational region logic is from
[Banerjee et al.](https://dl.acm.org/doi/10.1145/3551497).

## Intent

Relational verification asks whether two programs (or two runs of one
program) are related: equivalence of two ADT implementations, program
transformations preserving behavior, noninterference. WhyRel expresses this
with *bicommands* over an object-based language and discharges VCs through
Why3.

The goal here is to find out what that looks like as a **Strata DDM
dialect**:

- Bicommand syntax should be a small, declarative extension of Core, not a
  new language — Core's commands, expressions, and types come along for
  free via `import Core`.
- Verification should not require a new verifier. RRL lowers to
  `Core.Program` and hands off to `Strata.Core.verifyProgram`, the same
  pipeline every Core program uses.
- Diagnostics must point back at RRL source, not at generated Core.
- The dialect should live in its own package and be usable without
  modifying `Strata` or `Strata-CLI`, per Strata's repository-split
  philosophy (`docs/verso/IRTranslationPhilosophyDoc.lean`, issue #1168).

## State

Early but genuinely end-to-end: you can write a `.rrl.st` file and get
per-obligation pass/fail with source locations.

**Works today**

- `.rrl.st` concrete syntax, parsed by DDM from the `#dialect RRL` declaration
- `StrataDDM.Program` → `Core.Program` translation, with source positions preserved
- SMT-backed verification via Core's unmodified pipeline
- A standalone `rrl` CLI (`rrlVerify`, `rrlToCore`) with no `Strata-CLI` dependency

**Not yet**

- **Relational specifications.** There are no `Agree` pre/post-conditions or
  `bimodule`-style specs. The two sides are verified *independently*, so a
  goal like `a_left == a_right` cannot be stated. This is the main gap
  versus RelRL and the next thing worth building.
- **Objects, classes, methods, modules.** Each side is plain Core commands.
  There is no heap model — deliberately, since the forall-forall examples
  being targeted first don't need one.
- **A second bicommand operator.** `biembed` is the only one; nesting is
  plumbed through the translator but unexercised.
- **Tests.** The example is exercised by running the CLI by hand.

The whole dialect is currently three declarations:

```
dialect RRL;
import Core;

category Bicommand;
op biembed (left : Command, right : Command) : Bicommand => "(" left " | " right ")";
op command_bicommand (b : Bicommand) : Command => b;
```

## Quick start

Requires a sibling `Strata` checkout at `../Strata` (a path dependency) with
a matching `lean-toolchain`, and an SMT solver on `PATH` (cvc5 by default).

```console
$ lake build rrl
$ ./.lake/build/bin/rrl rrlVerify RRL/Examples/Swap.rrl.st
Swap.rrl.st(36, 4) [left_a_then_b]: ✅ pass
Swap.rrl.st(37, 4) [left_a_then_b]: ✅ pass
Swap.rrl.st(43, 4) [right_b_then_a]: ✅ pass
Swap.rrl.st(44, 4) [right_b_then_a]: ✅ pass
All 4 goals passed.
```

`rrl rrlToCore <file>` prints the translated Core program instead, so it can
be verified with any generic Core tool. `rrl --help` lists both commands and
their flags (`--check-mode`, `--solver`, `--vc-directory`, …, shared with
`strata verify`).

## Layout

| Path | Role |
| --- | --- |
| `RRL/DDMTransform/Grammar.lean` | the `#dialect RRL … #end` declaration |
| `RRL/DDMTransform/Translate.lean` | `StrataDDM.Program` → `Core.Program` |
| `RRL/Verify.lean` | translate, then `Strata.Core.verifyProgram` |
| `RRL/Cli.lean` | `rrlVerify` / `rrlToCore` command definitions |
| `Main.lean` | standalone `rrl` executable |
| `RRL/Examples/Swap.rrl.st` | ported from [RelRL `examples/all_all/swap`](https://github.com/dnaumann/RelRL/tree/main/examples/all_all/swap) |

`WORKFLOW.md` documents the full pipeline step by step, along with the design
decisions behind it (why lower to Core rather than to Imperative+Lambda, why
the translator hand-walks the DDM AST instead of using generated `ofAst`, and
why left and right are separate state spaces).

## License

Apache-2.0 OR MIT, matching Strata — see `LICENSE-APACHE` and `LICENSE-MIT`.
