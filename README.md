# StrataRelRL

An experimental [Strata](https://github.com/strata-org/Strata) dialect that
adds **bicommands** — paired left/right program fragments — on top of Strata
Core, and verifies them by lowering to Core and reusing Core's existing
SMT-backed verification pipeline unchanged. It ports
from **WhyRel** — the original OCaml implementation which lives at
[dnaumann/RelRL](https://github.com/dnaumann/RelRL) based on Why3 onto Strata,
starting with the forall-forall (2-safety) fragment described in
[Nagasamudram et al., TACAS 2023](https://link.springer.com/chapter/10.1007/978-3-031-30820-8_11);
the underlying relational region logic is from
[Banerjee et al.](https://dl.acm.org/doi/10.1145/3551497).

## Usage

Requires an SMT solver on `PATH` (cvc5 by default).

`Main.lean` + `RelRL/Cli.lean` define a self-contained `lean_exe` built on the
shared `Strata.Cli.Framework` from the `Strata` dependency, so no
`Strata-CLI` checkout is involved.

```console
$ lake exe relrl verify RelRL/Examples/Swap.relrl.st
Swap.relrl.st(14, 4) [left_a_then_b]: ✅ pass
Swap.relrl.st(15, 4) [left_a_then_b]: ✅ pass
Swap.relrl.st(21, 4) [right_b_then_a]: ✅ pass
Swap.relrl.st(22, 4) [right_b_then_a]: ✅ pass
Swap.relrl.st(25, 2) [agree_a]: ✅ pass
Swap.relrl.st(26, 2) [agree_b]: ✅ pass
All 6 goals passed.
```
`verify` accepts the same `--check-mode`/`--solver`/`--vc-directory`/etc. flags
as the generic `strata verify` command (`Strata.Cli.VerifyOptions`), and uses
the same exit-code scheme (0 = success, 2 = failures found, 3 = internal error).
A translation diagnostic also exits 3: the Core program verified would not be
the program written, so a clean obligation count must not read as success.

`relrl toCore <file>` prints the translated Core program instead, so it can
be verified with any generic Core tool. 

`relrl --help` lists both commands and their flags (`--check-mode`, `--solver`,
`--vc-directory`, …, shared with `strata verify`). (currently the help and error
text names `strata` rather than `relrl`. Fix is upstream)

## Layout

| Path | Role |
| --- | --- |
| `RelRL/DDMTransform/Grammar.lean` | the `#dialect RelRL … #end` declaration |
| `RelRL/DDMTransform/Translate.lean` | `StrataDDM.Program` → `Core.Program` |
| `RelRL/Verify.lean` | translate, then `Strata.Core.verifyProgram` |
| `RelRL/Cli.lean` | `verify` / `toCore` command definitions |
| `Main.lean` | standalone `relrl` executable |
| `RelRL/Examples` | Dialect examples |

[`docs/status.md`](docs/status.md) records what works today and what does not,
[`docs/workflow.md`](docs/workflow.md) documents the full pipeline step by step,
[`docs/design.md`](docs/design.md) records the design decisions behind the
dialect, and [`docs/issues.md`](docs/issues.md) records known defects.

## License

Apache-2.0 OR MIT, matching Strata — see `LICENSE-APACHE` and `LICENSE-MIT`.
