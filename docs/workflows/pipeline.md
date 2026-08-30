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

`RelRL/DDMTransform/Translate.lean` 

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
  `docs/design.md`.
- `lower_biproc` emits the `requires` assumptions, then the body, then the
  `ensures` obligations. `requires` is lowered against the *incoming* bindings
  and an empty bi-local set, matching its lack of `@[scope(…)]`; `ensures`
  against the bindings and bi-locals the body ends with. `lower_spec_clauses`
  handles both, differing only in `assume` versus `assert`.
- Over the body, `lower_biproc` folds `lower_bicommand`, accumulating a
  `BodyState`: the bindings, the bi-local names, and the statements not yet
  emitted. A relational `Assert` has to observe both sides of every bicommand
  before it, so `BodyState.flush` emits the pending lefts and then the pending
  rights each time one is reached, and again at the end.
- `lower_bicommand` handles the four forms. `bi_var` / `bi_var_left` /
  `bi_var_right` lower each side's `DeclList` through `lower_decl_list`, which
  puts it back in the `Core.varStatement` Core's own grammar wraps it in;
  nothing is primed, since the two names are distinct bindings already. `bi_sync` holds a *single*
  statement, which it lowers once and emits twice — unprimed left, primed
  right — so one source declaration yields the bi-local pair `a`/`a'`; it is
  also the only form that extends the bindings and the bi-local set. Declaring
  two bi-locals is two synchronized bicommands. `bi_embed` lowers each side from the
  bicommand's own incoming bindings and primes the right against its own
  declarations as well as the bi-locals. `bi_assert` flushes, then emits the
  formula.
- `prime_stmts` and `prime_expr` are the two halves of priming, both folds over
  Core's own substitution — `Block.substFvar`/`Block.renameLhs` for statements,
  `Lambda.LExpr.substFvar` for expressions — so no traversal of the Core AST is
  written here.
- `lower_rformula` lowers a relational formula to one Core `bool` expression.
  `Agree x` is the only lexical form (it names `x'`, which translation invents);
  everything else routes its Core expression through `Core.translateExpr` in the
  bi-local scope, then primes it if it is a right-hand fragment. Connectives
  become Core's own `boolAndOp`, `boolOrOp`, `boolImpliesOp`, `boolEquivOp`,
  `boolNotOp`. `top_conjuncts` peels a top-level `/\` first, so each conjunct
  becomes its own `assert`.
- `lower_spec_clauses` does the same for the `requires`/`ensures` clauses:
  `assume`s before the body, `assert`s after it.
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
block closes. Priming makes the two sides disjoint, so concatenating them is
ordinary self-composition — the standard encoding for the forall-forall
fragment, and sound precisely because after priming neither side can observe the
other.

Only *top-level* declarations of a side are primed. One nested inside an `if`
or `while` body stays block-scoped, so it can neither collide across sides nor
be named by a formula.

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
`verify_to_messages` is a convenience wrapper that formats both the
translation diagnostics and one `Message` per proof obligation.

