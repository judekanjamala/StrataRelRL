# Design decisions

> **Scope.** One bullet per decision: what was chosen, what was rejected, and
> why.

## Shape of the project

- **Own package, own CLI.** Strata's `docs/verso/IRTranslationPhilosophyDoc.lean`
  (issue #1168) has a dialect depend on `Strata`, never the reverse. Wiring RelRL
  into `Strata-CLI` was tried and abandoned: it spread the `Strata.Core`/`Core`
  namespace ambiguity into another repo's build.

- **Translate to Core, not to Imperative + Lambda.** Verification runs on the
  internal ASTs, but Core is the supported entry point that already wires up VC
  generation and SMT discharge — so lowering to `Core.Program` inherits the
  pipeline, mirroring `laurelToCore`.

- **Hand-walk the DDM AST; don't use `ofAst`.** No dialect translates through
  `#strata_gen`'s conversion — Core, C_Simp and Laurel all walk `Operation`/`Arg`
  by hand, which is what makes reusing `Core.getProgram` possible.

## Syntax

- **`Bicommand` is its own category, never a `Command`.** DDM parses only
  `Init.Command` at top level (`StrataDDM/Elab/Core.lean:1838`), so `biproc` is
  RelRL's only one. An injection back to `Command` would admit nesting
  (`<< << a | b >> | c >>`), so the sides hold Core `Statement`s, which no Core
  operator lets contain a `Command`. `Grammar.lean`; CLAUDE.md guards it.

- **The surface syntax follows WhyRel; the expression layer is Core's.** From
  `dnaumann/RelRL`'s `src/parser/parser.mly`. Three deviations:
  1. **Statements inside a side are Core's** — `i := 0;`, `int.add(a, b)`.
     Matching WhyRel means owning a statement grammar and translator, giving up
     the reuse of `Core.getProgram`.
  2. **`|- c -|`, not `|_ c _|`.** Forced by the lexer — below.
  3. **`<< c | c' >>`, not `( c | c' )`.** Preference: `(` is also Core's
     expression grouping, and `>>` cannot collide.

- **Two delimiters were settled by what DDM's lexer takes a character to
  start.** `_` starts an identifier (`Parser.lean:122`), so `_|` can never be a
  token — hence `-|` for the synchronized closer. And `|` opens a pipe-delimited
  identifier, SMT-LIB style (`Parser.lean:308`), which is also what prints a
  primed name as `|result'|`; so a `|` needs trailing whitespace, and
  `Var acc : int |;` runs to end of file as an unterminated identifier.

- **Every formula operand is a Core expression, elaborated by DDM**, So RelRL
  owns no expression grammar, and an operand naming nothing is DDM's error, at
  its column, before lowering.

- **One form reaches across the two programs, and it is `Let`.** Three were
  tried. `Rel int.gt (l | r)` picked the side by *position*, as `l =:= r` does;
  position reaches only a whole operand, never `[< i <] + [> j >]`, so `BiExp`
  was added under it, marking sides at the leaves as WhyRel does. Both are gone.
  `BiExp` could only ever be an `int` shorthand — reaching every Core expression
  means mirroring some sixty operator forms (`bv` widths, `Map`, `Sequence`,
  `str`, `re`), which is the reuse of `Core.getProgram` spent. `Let` needs three
  ops and has no ceiling: the names are Core *bound* variables, so Core's own
  expressions combine them at any type with nothing primed.

- The one-sided BiWhile steps are this translator's own `project` mode applied
  to the body, which is why that mode is more than a printing aid.
  `Bicommands.lean`.

- **A call inside a bicommand is Core's `call`, and needed nothing new.** A
  split's sides are Core `Statement`s, and Core resolves a call against the
  callee's `spec` — so relating two programs that call the same procedures in
  different orders just works. The reuse argument paying off, not a feature.

- **A `biproc` is called by `|- Call m (…) | (…) -| ;`, and lowers to *one* Core
  call.** The callee's `biproc` is already one Core procedure whose contract
  *is* the relational one, so WhyRel's `|_ m() _|` semantics falls out. Two
  calls would have used two unary specs, which is what a split already does.
  `Call` is used instead of `call` to keep with the dialect's other keywords and
  stays distinct from a Core call inside a `|- … -|`; lowercase would parse,
  since DDM's longest match separates `bi_sync` from `bi_call`. Parens per side,
  as the declaration has. Forced is the translator's arity check: Core's message
  arrives after the lists are fused and names neither side nor position.

- **A synchronized `biproc` call is refused inside `While e|e' . p|p' do`.**
  That form's one-sided steps are its body's `project`ions, and a projected
  `Call` would name the *fused* procedure with one side's arguments. Giving it
  meaning needs a unary contract per side, which a relational `ensures` cannot
  supply and RelRL, having no module structure, cannot declare — so it is refused
  with a located error. Lockstep `While`, `WhileL` and `WhileR` don't project.

## Specs

- **A biproc's parameters are a Core `Bindings` per side**, so `out`, `inout`
  and `translateProcBindings` come from Core unchanged. The cost is spelling:
  parens per side, and a named `out` rather than WhyRel's implicit `result` —
  which a translator cannot bind into *DDM's* elaborator. Naming the binding
  `result` recovers WhyRel's spelling exactly.

- **A top-level `/\` splits** into one obligation per conjunct, which reads far
  better than one opaque `&&`. `{ … }` is transparent to the peeling; every
  other connective is opaque, since its parts are not separately provable.

  `Both (e)` splits too, by desugaring to `<| e <] /\ [> e |>` before lowering —
  same Core, but the peeling reaches it, so a failure names the program it
  happened in. Under any other connective it stays opaque.

## Translation

- **The sides are flattened, not nested.** An `ensures` naming both sides is
  impossible while they sit in `left:`/`right:` blocks, since a Core block's
  locals vanish when it closes. Priming makes the two disjoint, so one block is
  the standard forall-forall encoding — sound precisely because neither side can
  then observe the other, which the next bullet has to deliver. `State.lean`.

- **The rename is driven by what a fragment mentions, not by a list of expected
  names.** Soundness needs priming *total* over the fragment: one name left
  unrenamed is one variable the two programs silently share. Driving it from the
  fragment makes totality structural rather than a list someone maintains.

  Core is what makes that possible — it has no top-level variables, since a
  constant is a 0-ary function lowering to `.op`, never `.fvar`. So every name
  these helpers reach is one of the two programs' locals. An *expected*-name list
  would let anything off it fall through to the left program's variable.
  Globals are the one thing outside that reach, and a defect rather than a
  boundary — [`issues.md`](issues.md), "A top-level declaration is shared".

- **The translator scope-checks each side, because DDM cannot.** DDM threads one
  linear typing context, so a reference resolves without regard to which side of
  the `|` it sits on, and Core's `Lhs` is lexical, so a side may even *assign* to
  a name it cannot read. `BodyState.check_side`, with DDM's own range.
  `State.lean`.

- **A `biproc` is lowered to Core terms, not rewritten into DDM ones.** The
  alternative — rewriting `biproc` into a Core `command_procedure` in
  `Desugar.lean` — would retire the reconstructed `top` and `misaligning_command?`
  with it. Two things stop it.

  **Priming**, which is not a rename there: a `|- c -|` holds one fragment both
  programs run, so it must become two at different binder positions —
  duplication with re-indexing, and only `TypeExprF` has an `incIndices`. On Core
  terms it is `substFvar`/`renameLhs` over names. And **order**: `translateExpr`
  resolves a body's `.fvar i` by indexing the *translated* declarations, so a
  rewrite producing them could not have run first. [`issues.md`](issues.md)
  costs it out.

- **Sugar is rewritten before lowering, not during it.** Doing it in
  `lower_bicommand` means writing the sugar's lowering against all of `Mode`; a
  pass over the parsed program means one rewrite, seen by every mode and by
  `bi_while`'s re-lowering of its own body. `Desugar.lean`.

  The pass is over an *elaborated* program, which is the whole constraint: an
  expression is already `ExprF.bvar i` against the `@[scope(…)]` chain, so a
  rewrite changing how many binders enclose a subterm silently rebinds every
  index, and only `TypeExprF` has an `incIndices` to repair with. Hence the rule
  on the module: no rewrite introduces, drops, reorders or lifts out of a binder.
  That admits WhyRel's else-less `If` and rules out any sugar wanting a fresh
  temporary, which belongs in the lowering instead.

- **Top-level Core commands are translated in one pass.** A `.fvar i` indexes the
  program's top-level declarations; translating each command in its own singleton
  program left that array empty, so every cross-reference resolved to declaration
  0 — `axiom [p]: int.gt(bound, 0)` became `int.gt(0, 0)`, a *false* axiom making
  every obligation vacuous. `Program.lean`.

- **Lowering runs inside Core's `TransM`, threading `TransBindings`.** Each side
  as its own singleton `StrataDDM.Program` cannot survive a shared elaboration
  scope: a de Bruijn index from an enclosing context means nothing in a fresh
  program, and Core miscompiles before aborting. `TransM`, `translateStmt` and
  `translateBlock` are public, so the translator follows the grammar's
  `@[scope(…)]` chain exactly — by hand, and the two must be kept in step.
