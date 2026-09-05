# StrataRelRL

> **Scope.** What the project is, how to run it, and where everything is
> documented. Details live in `docs/` — see the table below.

An experimental [Strata](https://github.com/strata-org/Strata) dialect that adds
**bicommands** — paired left/right program fragments — on top of Strata Core, and
verifies them by lowering to Core and reusing Core's SMT-backed pipeline
unchanged. It ports **WhyRel** ([dnaumann/RelRL](https://github.com/dnaumann/RelRL),
OCaml on Why3) onto Strata, starting with the forall-forall (2-safety) fragment
of [Nagasamudram et al., TACAS 2023](https://link.springer.com/chapter/10.1007/978-3-031-30820-8_11);
the underlying relational region logic is from
[Banerjee et al.](https://dl.acm.org/doi/10.1145/3551497).

## Usage

Requires an SMT solver on `PATH` (cvc5 by default).

`Main.lean` + `RelRL/Cli/` define a self-contained `lean_exe` on the shared
`Strata.Cli.Framework`, so no `Strata-CLI` checkout is involved. One module per
command, matching [`docs/workflows.md`](docs/workflows.md).

```console
$ lake exe relrl verify RelRL/Examples/WhyRel/Factorial.relrl.st
Factorial.relrl.st(16, 2) [insertLoopInvAssert_entry_invariant_loop_0_0_while_1_align]: ✅ pass
…
Factorial.relrl.st(10, 2) [ensures_1]: ✅ pass
Factorial.relrl.st(11, 2) [ensures_3]: ✅ pass
All 15 goals passed.
```

`verify` takes the same `--check-mode`/`--solver`/`--vc-directory`/… flags as the
generic `strata verify` (`Strata.Cli.VerifyOptions`) and the same exit codes
(0 = success, 2 = failures, 3 = internal error). A translation diagnostic also
exits 3: the Core program verified would not be the program written, so a clean
obligation count must not read as success.

`relrl toCore <file>` prints the translated Core program instead, so it can be
verified with any generic Core tool.

`relrl project <file> --side left|right` prints the Core program for *one* side
of every `biproc` — the unary program that side denotes alone, without the other
side or the relational `ensures` (which names both, so it means nothing about
one). Nothing shares its scope, so the right side keeps its source names. Useful
for reading what each side says, and for checking its own unary specs.

`relrl --help` lists all three commands and their flags. The help and error text
currently names `strata` rather than `relrl`; the fix is upstream —
[`docs/issues.md`](docs/issues.md).

## Layout

| Path | Role |
| --- | --- |
| `RelRL.lean` | library root: grammar, translation, verification, no CLI |
| `RelRL/DDMTransform/Grammar.lean` | the `#dialect RelRL … #end` declaration |
| `RelRL/DDMTransform/Translate/` | `StrataDDM.Program` → `Core.Program`, one module per stage |
| `RelRL/DDMTransform/Translate.lean` | imports the six, so callers see one module |
| `RelRL/Verify.lean` | translate, then `Strata.Core.verifyProgram` |
| `RelRL/Cli/Common.lean` | parsing a `.relrl.st` file, diagnostics, exit codes |
| `RelRL/Cli/Verify.lean` | the `verify` command |
| `RelRL/Cli/ToCore.lean` | the `toCore` command |
| `RelRL/Cli/Project.lean` | the `project` command |
| `RelRL/Cli.lean` | imports the four, so `Main.lean` sees one module |
| `Main.lean` | standalone `relrl` executable |
| `RelRL/Examples` | dialect examples, one per feature; `README.md` is the regression baseline |
| `RelRL/Examples/WhyRel` | WhyRel's `examples/all_all` case studies, ported |

Each doc opens with a **Scope** note saying what belongs in it and where
everything else goes; keep them honest when adding.

| Doc | Holds |
| --- | --- |
| [`docs/status.md`](docs/status.md) | what works today, and every difference from WhyRel |
| [`docs/workflows.md`](docs/workflows.md) | how the workflows relate; each command is documented in its own module |
| [`docs/design.md`](docs/design.md) | the design decisions and why they went that way |
| [`docs/issues.md`](docs/issues.md) | known defects, each traced to its root cause |

## License

Apache-2.0 OR MIT, matching Strata — see `LICENSE-APACHE` and `LICENSE-MIT`.
