# StrataRelRL

An experimental [Strata](https://github.com/strata-org/Strata) dialect that
adds **bicommands** — paired left/right program fragments — on top of Strata
Core, and verifies them by lowering to Core and reusing Core's existing
SMT-backed verification pipeline unchanged.

The dialect is called `RelRL`, after *relational region logic*. It ports ideas
from **WhyRel** — the original OCaml implementation which lives at
[dnaumann/RelRL](https://github.com/dnaumann/RelRL) based on Why3 onto Strata,
starting with the forall-forall (2-safety) fragment described in
[Nagasamudram et al., TACAS 2023](https://link.springer.com/chapter/10.1007/978-3-031-30820-8_11);
the underlying relational region logic is from
[Banerjee et al.](https://dl.acm.org/doi/10.1145/3551497).


## Current State

Early but genuinely end-to-end: you can write a `.relrl.st` file and get
per-obligation pass/fail with source locations.

**Works today**

- `.relrl.st` concrete syntax, parsed by DDM from the `#dialect RelRL` declaration
- `StrataDDM.Program` → `Core.Program` translation, with source positions preserved
- SMT-backed verification via Core's unmodified pipeline
- A standalone `relrl` CLI (`relrlVerify`, `relrlToCore`) with no `Strata-CLI` dependency

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
dialect RelRL;
import Core;

category Bicommand;
op biembed (left : Command, right : Command) : Bicommand => "(" left " | " right ")";
op command_bicommand (b : Bicommand) : Command => b;
```

## Quick start

Requires a sibling `Strata` checkout at `../Strata` (a path dependency) with
a matching `lean-toolchain`, and an SMT solver on `PATH` (cvc5 by default).

```console
$ lake build relrl
$ ./.lake/build/bin/relrl relrlVerify RelRL/Examples/Swap.relrl.st
Swap.relrl.st(36, 4) [left_a_then_b]: ✅ pass
Swap.relrl.st(37, 4) [left_a_then_b]: ✅ pass
Swap.relrl.st(43, 4) [right_b_then_a]: ✅ pass
Swap.relrl.st(44, 4) [right_b_then_a]: ✅ pass
All 4 goals passed.
```

`relrl relrlToCore <file>` prints the translated Core program instead, so it can
be verified with any generic Core tool. `relrl --help` lists both commands and
their flags (`--check-mode`, `--solver`, `--vc-directory`, …, shared with
`strata verify`).

## Layout

| Path | Role |
| --- | --- |
| `RelRL/DDMTransform/Grammar.lean` | the `#dialect RelRL … #end` declaration |
| `RelRL/DDMTransform/Translate.lean` | `StrataDDM.Program` → `Core.Program` |
| `RelRL/Verify.lean` | translate, then `Strata.Core.verifyProgram` |
| `RelRL/Cli.lean` | `relrlVerify` / `relrlToCore` command definitions |
| `Main.lean` | standalone `relrl` executable |
| `RelRL/Examples/Swap.relrl.st` | ported from [RelRL `examples/all_all/swap`](https://github.com/dnaumann/RelRL/tree/main/examples/all_all/swap) |

`WORKFLOW.md` documents the full pipeline step by step, along with the design
decisions behind it (why lower to Core rather than to Imperative+Lambda, why
the translator hand-walks the DDM AST instead of using generated `ofAst`, and
why left and right are separate state spaces).

## License

Apache-2.0 OR MIT, matching Strata — see `LICENSE-APACHE` and `LICENSE-MIT`.
