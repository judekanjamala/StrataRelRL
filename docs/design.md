# Design decisions

> **Scope.** One bullet per decision: what was chosen, what was rejected, and
> why.

## Shape of the project

- **Own package, own CLI.** Strata's `docs/verso/IRTranslationPhilosophyDoc.lean`
  ("Relation to the proposed repository split", issue #1168) has a dialect and
  its translation-to-Core depend on `Strata`, never the reverse. The
  self-contained `lean_exe relrl` extends that to tooling: wiring RelRL into
  `Strata-CLI` was tried first and abandoned once it spread the
  `Strata.Core`/`Core` namespace ambiguity into another repo's build.

- **Translate to Core, not to Imperative + Lambda.** Verification runs on the
  internal Lambda/Imperative ASTs, but Core is the supported entry point that
  already wires up VC generation and SMT discharge. Lowering to `Core.Program`
  inherits that pipeline instead of hooking up a verifier, mirroring how
  `laurelToCore` separates Laurel translation from Core verification.

- **Hand-walk the DDM AST; don't use `ofAst`.** `#strata_gen` produces a typed
  Lean AST and an `ofAst` conversion, but no dialect in Strata translates
  through it — Core, C_Simp and Laurel all walk `Operation`/`Arg` by hand.
  Following that is what makes reusing `Core.getProgram` possible.

## Syntax

- **`Bicommand` is its own category, and never a `Command`.** DDM parses
  `Init.Command` at a program's top level (`StrataDDM/Elab/Core.lean:1838`), so
  a category nothing reaches is dead. `biproc` is therefore RelRL's only
  `Command`, and a `Bicommand` appears only inside its body. An identity
  injection `op … (b : Bicommand) : Command` would admit nesting — with
  `Command`-typed sides `<< << a | b >> | c >>` parses — so the sides hold Core
  `Statement`s, which no Core operator lets contain a `Command`.
  `Grammar.lean`; CLAUDE.md guards it.

- **The surface syntax follows WhyRel; the expression layer is Core's.** From
  `dnaumann/RelRL` (`src/parser/parser.mly`). Three deviations:
  1. **Statements inside a side are Core's.** `i := 0;` not `i := 0`,
     `int.add(a, b)` not `a + b`. Matching WhyRel means writing RelRL's own
     statement grammar and translator, giving up the reuse of `Core.getProgram`.
  2. **`|- c -|`, not `|_ c _|`.** Forced: DDM's lexer cannot tokenize `_|`.
  3. **`<< c | c' >>`, not `( c | c' )`.** Preference — `(` is also Core's
     expression grouping, and `>>` cannot collide since Core has no infix `>`.


- **A formula's operands are Core expressions, elaborated by DDM.** So
  `<| int.gt(n, 0) <]` and `l =:= r` work without RelRL owning an expression
  grammar. `Agree x` is the exception and takes an `Ident`: it names the pair
  `x`/`x'`, and `x'` exists only after lowering, so there is nothing for DDM to
  resolve. `check_formula` checks that operand instead. `Formulas.lean`.

- The one-sided BiWhile steps are this translator's own `project` mode applied to the
  body, which is why that mode is more than a printing aid. `Bicommands.lean`.

- **A call inside a bicommand is Core's `call`, and needed nothing new.** A
  split's sides are Core `Statement`s and a call is one, so relating two
  programs that call the same procedures in different orders works because Core
  resolves a call against the callee's `spec`. This is the reuse argument paying
  off rather than a feature that was added.

- **A `biproc` is called by `|- Call m (…) | (…) -| ;`, and lowers to *one*
  Core call.** WhyRel's `|_ m() _|` on a bimethod uses that method's relational
  spec; the same thing here falls out of self-composition, because the callee's
  `biproc` already became one Core procedure whose contract *is* the relational
  one. Two calls would have used two unary specs, which is what a split already
  does. The fused procedure's inputs are the left side's then the right's, and
  so are its outputs, which is exactly the order the two argument lists
  concatenate in — so the call site needs no reordering, only the usual priming
  of the right side. This is the form that makes a `biproc`'s spec a hypothesis
  rather than only an obligation.

  Three spellings were forced. `Call` rather than Core's `call`, because after
  `|- ` a Core `call` statement is already a live alternative and the callee is
  not a Core procedure. Parens per side, for the same reason the declaration has
  them. And an arity check in the translator, because Core's own message for a
  mismatch arrives after the two lists have been fused into one and so names
  neither the side nor a position.

- **A synchronized `biproc` call is refused inside `While e|e' . p|p' do`.**
  That form's one-sided steps are its body's `project`ions, and a projected
  `Call` would name the *fused* procedure with one side's arguments.
  Giving it a meaning needs a unary contract per side, which a `biproc` does not
  have and cannot be given: a relational `ensures` says nothing about one
  program alone. WhyRel has the unary specs because its bimethods live in a
  module that declares them; RelRL has no module structure, so the form is
  refused with a located error rather than mis-lowered. The lockstep `While`,
  `WhileL` and `WhileR` do not project their bodies and take it fine.

## Specs


- **A biproc's parameters are a Core `Bindings` per side.** `out`, `inout` and
  `translateProcBindings` then come from Core unchanged. The cost is the
  spelling: parens go around each side rather than the pair. The return is a
  named `out` binding, not WhyRel's implicit `result`, because `result` would
  have to be bound in *DDM's* elaborator for a spec to name it; naming the
  binding `result` recovers WhyRel's spelling exactly.

- **A top-level `/\` splits** into one obligation per conjunct, because that
  reads far better in the verifier's output than one opaque `&&`. `{ … }` is
  transparent to the peeling; every other connective is opaque, since its parts
  are not separately provable.

## Translation

- **The sides are flattened, not nested.** An `ensures` naming both sides is
  impossible while they sit in `left:`/`right:` blocks, since a Core block's
  locals are invisible once it closes. Priming makes the two disjoint, so
  emitting both into one block is the standard forall-forall encoding — sound
  precisely because after priming neither side can observe the other. That
  soundness needs the rename to be *total* over the fragment, which is why it is
  driven by what the fragment mentions rather than a list of expected names.
  `Priming.lean`; CLAUDE.md's second invariant.

- **The translator scope-checks each side, because DDM cannot.** DDM threads one
  linear typing context, so a reference resolves without regard to which side of
  the `|` it sits on; and Core's `Lhs` is lexical, so a side may even *assign* to
  a name it cannot read. `BodyState.check_side` reports that with the source
  range DDM would have used. `State.lean`.

- **Top-level Core commands are translated in one pass.** A `.fvar i` indexes
  the program's top-level declarations. Translating each command in its own
  singleton program left that array empty, so every cross-reference resolved to
  declaration 0 — `axiom [p]: int.gt(bound, 0)` became `int.gt(0, 0)`, a *false*
  axiom that made every obligation vacuously provable. `Program.lean`.

- **Lowering runs inside Core's `TransM`, threading `TransBindings`.** Each side
  as its own singleton `StrataDDM.Program` cannot survive a shared elaboration
  scope: a de Bruijn index from an enclosing context means nothing in a fresh
  program, and Core miscompiles before aborting. `TransM`, `translateStmt` and
  `translateBlock` are public and thread bindings in and out, so the translator
  follows the grammar's `@[scope(…)]` chain exactly — by hand, and the two must
  be kept in step.
