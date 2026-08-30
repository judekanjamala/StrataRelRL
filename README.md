# StrataRelRL

> **Scope.** What the project is, how to run it, and where everything is
> documented. Details live in `docs/` — see the table below.

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
$ lake exe relrl verify RelRL/Examples/Assertions.relrl.st
Assertions.relrl.st(49, 2) [assert_1_1]: ✅ pass
Assertions.relrl.st(49, 2) [assert_1_2]: ✅ pass
Assertions.relrl.st(21, 2) [ensures_1]: ✅ pass
Assertions.relrl.st(21, 2) [ensures_2]: ✅ pass
Assertions.relrl.st(21, 2) [ensures_3]: ✅ pass
Assertions.relrl.st(21, 2) [ensures_4]: ✅ pass
Assertions.relrl.st(21, 2) [ensures_5]: ✅ pass
Assertions.relrl.st(21, 2) [ensures_6]: ✅ pass
Assertions.relrl.st(21, 2) [ensures_7]: ✅ pass
Assertions.relrl.st(21, 2) [ensures_8]: ✅ pass
Assertions.relrl.st(21, 2) [ensures_9]: ✅ pass
Assertions.relrl.st(21, 2) [ensures_10]: ✅ pass
All 12 goals passed.
```
`verify` accepts the same `--check-mode`/`--solver`/`--vc-directory`/etc. flags
as the generic `strata verify` command (`Strata.Cli.VerifyOptions`), and uses
the same exit-code scheme (0 = success, 2 = failures found, 3 = internal error).
A translation diagnostic also exits 3: the Core program verified would not be
the program written, so a clean obligation count must not read as success.

`relrl toCore <file>` prints the translated Core program instead, so it can
be verified with any generic Core tool. 

`relrl project <file> --side left|right` prints the Core program for *one* side
of every `biproc` — the unary program that side denotes on its own, with neither
the other side nor the relational `ensures` (which names both sides, so it means
nothing about one). Nothing shares its scope, so the right side keeps its source
names rather than being primed. Useful for reading what each side actually says,
and for checking a side's own unary specs with a generic Core tool.

`relrl --help` lists all three commands and their flags (`--check-mode`, `--solver`,
`--vc-directory`, …, shared with `strata verify`). (currently the help and error
text names `strata` rather than `relrl`. Fix is upstream)

## Layout

| Path | Role |
| --- | --- |
| `RelRL/DDMTransform/Grammar.lean` | the `#dialect RelRL … #end` declaration |
| `RelRL/DDMTransform/Translate.lean` | `StrataDDM.Program` → `Core.Program` |
| `RelRL/Verify.lean` | translate, then `Strata.Core.verifyProgram` |
| `RelRL/Cli.lean` | `verify` / `toCore` / `project` command definitions |
| `Main.lean` | standalone `relrl` executable |
| `RelRL/Examples` | Dialect examples |

Each doc opens with a **Scope** note saying what belongs in it and where
everything else goes; keep them honest when adding.

| Doc | Holds |
| --- | --- |
| [`docs/status.md`](docs/status.md) | what works today, and every difference from WhyRel |
| [`docs/workflows/`](docs/workflows/) | one file per workflow — build, verify, toCore, project — plus the pipeline they share |
| [`docs/design.md`](docs/design.md) | the design decisions and why they went that way |
| [`docs/issues.md`](docs/issues.md) | known defects, each traced to its root cause |

## License

Apache-2.0 OR MIT, matching Strata — see `LICENSE-APACHE` and `LICENSE-MIT`.
