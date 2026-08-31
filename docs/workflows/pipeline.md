# The shared pipeline

> **Scope.** The stages every workflow walks, from source text to
> `Core.Program`. Per-command behaviour belongs in that command's file; why a
> stage works the way it does belongs in [`../design.md`](../design.md).

Last verified end-to-end: 2026-08-30 (`lake build relrl`, then `relrl verify` on
all four examples in `RelRL/Examples` → 12/12, 4/4, 2/2 and 2/2 goals passed),
against `Strata` upstream `main`.

Every RelRL workflow walks stages 1 and 2 below and differs only in what it does
with the resulting `Core.Program`. This file documents the shared stages; the
per-workflow files in this directory document the differences. Start from
[`README.md`](README.md).

## 1. Concrete RelRL program to `StrataDDM.Program`

`RelRL/DDMTransform/Grammar.lean` declares the dialect with `#dialect … #end`.
That declaration is elaborated at build time, not at run time — see
[`build.md`](build.md) for how the grammar becomes a compiled constant and what
that implies for editing it.

`build_relrl_dialect_file_map` preloads the `Core` and `RelRL` dialect constants
(plus the DDM builtins) into the `DialectFileMap`, so `.relrl.st` files parse
without any `--include` search path; `--include` is still accepted for extra
dialects.

`StrataDDM.readStrataText` parses the program text. It is the inbuilt parser and
produces a generic `StrataDDM.Program` — dialect-agnostic DDM AST, every node
carrying its `SourceRange` and dialect-declared metadata.

## 2. `StrataDDM.Program` → `Core.Program` (`RelRL.DDMTransform.Translate`)

One module per stage under `RelRL/DDMTransform/Translate/`, in dependency
order, with `Translate.lean` importing them:

| Module | Holds |
|---|---|
| `Diagnostics` | `TranslateM` and the `Message` accumulator |
| `Priming` | which names a fragment mentions, and renaming them apart |
| `Formulas` | `lower_rformula`, `bool_app`, `top_conjuncts` |
| `State` | `Side`, `Mode`, `BodyState`, and the per-side and formula checks |
| `Bicommands` | `lower_bicommand`, the fold over a body |
| `Program` | specs, parameters, and the top-level walk |

- `translate_program_with` walks each top-level `Operation` in `p.commands`. A
  `RelRL.biproc` becomes a Core procedure *of the same name*, whose body is the
  lowered bicommand sequence; everything else is ordinary embedded Core syntax,
  delegated straight to Core's own `Core.getProgram`.
- **Lowering runs inside Core's `TransM`**, one run per `biproc`, seeded with
  `p.globalContext`. `lower_side` calls `Core.translateBlock` directly — wrapping
  the side's statement sequence in a synthetic `Core.block`, re-tagged `.newline`
  because `translateBlock` pattern-matches `.seq _ .newline` — and threads the
  `TransBindings` it returns into the next side. That threading has to mirror the
  `@[scope(…)]` chain in `Grammar.lean` exactly; see `docs/design.md` for what
  breaks when it does not.
- `translate_program_with` first translates every non-`biproc` command in **one**
  `translateCoreDecls` pass, so Core's binding state threads across them, and
  lowers each `biproc` against the bindings that produces. Doing it one command
  at a time left every cross-reference resolving to declaration 0 — see
  `docs/design.md`. The binding list is reconstructed from the decls that pass
  returns, which holds only while each command contributes exactly one;
  `misaligning_command?` refuses the two that do not, in any mode, rather than
  lower a body against a short list — [`issues.md`](../issues.md).
- `lower_params` turns each side's Core `Bindings` into the procedure's inputs
  and outputs through Core's own `translateProcBindings`, primes the right
  side's names, and hands back both as `DeclName`s so the per-side checks treat
  a parameter as declared. Under `project` only the kept side survives,
  unprimed.
- `lower_biproc` produces the procedure's signature, its contract and its body.
  Both spec clauses are lowered against the parameters alone — never the body's
  bindings — and become Core's `preconditions`/`postconditions`, so a spec
  cannot name a bi-local and `old x` means an `inout` parameter's entry value.
  `lower_spec_clauses` handles both, differing only in which field they land in.
- Over the body, `lower_biproc` folds `lower_bicommand`, accumulating a
  `BodyState`: the bindings, what has been declared on each side, and one output
  stream. `BodyState.emit` appends a bicommand's left statements and then its
  right ones, so the two programs interleave per element rather than being
  batched per side; `docs/design.md` says why that distinction is not cosmetic.
  A relational `Assert` therefore sees both sides as they stand simply by being
  emitted where it appears.
- `lower_bicommand` handles the four forms. `bi_var` / `bi_var_left` /
  `bi_var_right` lower each side's `DeclList` through `lower_decl_list`, which
  puts it back in the `Core.varStatement` Core's own grammar wraps it in, and
  prime the right side's names as every other form does. `bi_sync` holds a *single*
  statement, which it lowers once and emits twice — unprimed left, primed
  right — so one source declaration yields the bi-local pair `a`/`a'`.
  Declaring two bi-locals is two synchronized bicommands. `bi_embed` lowers each
  side from the bicommand's own incoming bindings. `bi_assert` and `bi_assume`
  emit the formula as an `assert` or an `assume`.
- The compound forms — `bi_if`, `bi_if_then`, `bi_if4`, `bi_while`,
  `bi_while_lockstep`, `bi_while_left`, `bi_while_right` — lower their nested
  bicommand sequences through `seq_body`, which runs the same fold into a fresh
  accumulator. Declarations inside do not come back out, since
  the sequence becomes a Core block; the assert and assume counters do, so
  labels stay unique across the body. `seq_body` takes its own `Mode` because
  `bi_while` lowers its body three times — fused, and once per side for the
  steps only one side takes. `docs/design.md` has each form's lowering.
- Each declaring form also records what it declared, under its Core name, in
  `BodyState.declared`. Self-composition fuses both programs into one Core
  scope, so that name is what has to be unique; a repeat is a located
  `.userError` in `BodyState.diagnostics`, which `lower_biproc` returns
  alongside the statements. Only `.verify` fuses, so `.project` skips the check
  — one unary program is Core's to check.
- `prime_stmts` and `prime_expr` are the two halves of priming, both folds over
  Core's own substitution — `Block.substFvar`/`Block.renameLhs` for statements,
  `Lambda.LExpr.substFvar` for expressions — so no traversal of the Core AST is
  written here. What they rename is *everything the fragment mentions*, from
  `fragment_names` / `expr_names`, which read Core's `HasVarsImp` and `HasFvars`
  rather than a list threaded through `BodyState`; CLAUDE.md says why that
  totality is the point. The fold is longest-name-first, so a fragment holding
  both `n` and `n'` does not prime `n` twice.
- `lower_rformula` lowers a relational formula to one Core `bool` expression.
  `Agree x` is the only lexical form (it names `x'`, which translation invents);
  everything else routes its Core expression through `Core.translateExpr` in the
  bindings in scope, then primes it if it is a right-hand fragment. Connectives
  become Core's own `boolAndOp`, `boolOrOp`, `boolImpliesOp`, `boolEquivOp`,
  `boolNotOp`. `top_conjuncts` peels a top-level `/\` first, so each conjunct
  becomes its own `assert`.
- `lower_spec_clauses` does the same for the `requires`/`ensures` clauses, which
  become `Core.Procedure.Check`s in the procedure's `spec` rather than
  statements in its body.
- Translation runs in `TranslateM` (a `StateM` over an `Array Message`), so
  broken invariants produce diagnostics rather than panics, and source positions
  survive via `Imperative.MetaData.ofSourceRange`. Core's own error strings from
  each `TransM.run` are folded into the same diagnostics.

### Projection: one side on its own

`translate_program_with` takes a `Mode`, and the pipeline above is its
`.verify` case — what `translate_program`, and so `verify`, uses. The
other case, `.project side`, drops everything that exists only because the two
sides share a scope:

- `lower_bicommand` keeps that side's statements from every bicommand, in
  order, and nothing of the other side. A synchronized `|- … -|` runs on both
  sides, so it is kept whole and emitted once.
- Nothing is renamed. Priming exists to keep the sides apart inside one
  procedure; with one side alone there is nobody to collide with, so the right
  projection keeps its source names too.
- The `ensures` clause and every `Assert { R }` are dropped rather than
  lowered. A relational formula names both sides, so it says nothing about one
  side alone.

The result is an ordinary unary `Core.Program` — one procedure per `biproc`,
under the `biproc`'s own name — which is what `relrl project <file> --side
left|right` prints. The two projections are the two programs the relational
spec talks about.

### Why the sides are flattened rather than nested

The sides are not `left:`/`right:` sub-blocks, because a relational formula has
to name both sides at once and a Core block's locals are invisible once the
block closes. Priming makes the two sides disjoint, so emitting both into one
list is the standard encoding for the forall-forall fragment, sound precisely
because after priming neither side can observe the other. The order is
per bicommand — each element's left statements, then its right ones.

Every variable a right-hand fragment mentions is primed, at any depth — one
declared inside an `if` or `while` body included, so the two sides stay disjoint
without relying on Core's block scoping to separate them. `top_level_declared`
survives only for the collision check, where block-scoped names are not at
stake.

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

`Strata.Core.verifyProgram` runs Core's existing VC-generation and
SMT-discharge pipeline unmodified. A fatal translation diagnostic means the Core
program is not the one the source denotes, so verification is skipped rather
than run on it.

