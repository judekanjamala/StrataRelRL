# Design decisions

> **Scope.** One bullet per decision: what was chosen, what was rejected, and
> why. No usage, no mechanics — [`status.md`](status.md) says what exists,
> [`issues.md`](issues.md) what is broken, `CLAUDE.md` what bites when editing,
> and the code says how. Each bullet names the file that implements it.

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

- **Two layers, and no token shared between them.** A one-state Core expression
  spells its connectives `&&`, `||`, `!`; a relational formula spells them
  `/\`, `\/`, `~`, `=>`, `<=>`. The parser never has to decide which layer an
  operator belongs to, and neither does a reader. Grouping in a formula is
  `{ … }`, since `Both (e)` already spends `( … )` on a Core expression.

- **A formula's operands are Core expressions, elaborated by DDM.** So
  `<| int.gt(n, 0) <]` and `l =:= r` work without RelRL owning an expression
  grammar. `Agree x` is the exception and takes an `Ident`: it names the pair
  `x`/`x'`, and `x'` exists only after lowering, so there is nothing for DDM to
  resolve. `check_formula` checks that operand instead. `Formulas.lean`.

- **Every relational form is written with source names.** No form makes the user
  write a prime: `Both (i == n)` lowers to `i == n && i' == n'`, and where the
  sides genuinely differ `l =:= r` relates a left expression to a right one.
  That is WhyRel's spelling, and it keeps `'` out of the surface syntax.

## What the bicommands mean

- **`Var` is the only declaration form, and the only one that extends the
  scope.** WhyRel draws the same line: its `|_ … _|` holds an `atomic_command`,
  a grammar with no declaration form. Writing the same name on both sides is how
  you say *both programs have this variable*, which is what `Agree` and `Both`
  need. `Grammar.lean`.

- **Conditionals collapse to one Core `if`, paid for by an obligation.**
  `If e|e'` asserts `e <=> e'` and then puts both sides under a single `if`.
  Two `if`s would need no assert, but would also stop a bicommand inside a
  branch from relating the two states, which is the point of the form. `If4` is
  for guards that need not agree and pays with four branches instead.
  `Bicommands.lean`, following WhyRel's `compile_bicommand`.

- **A loop's alignment guards decide who steps; the invariant rules out
  deadlock.** `While e|e' . p|p'` becomes one loop guarded by `e \/ e'`, whose
  body dispatches to the left projection, the right projection, or both. The
  alignment condition is an *invariant*, not an assert: it is what rules out a
  state where a side must step and its guard forbids it — WhyRel's Fault. The
  one-sided steps are this translator's own `project` mode applied to the body,
  which is why that mode is more than a printing aid. `Bicommands.lean`.

- **A bicommand sequence is an alignment, and lowering interleaves per
  element.** `(l₁|r₁); (l₂|r₂)` becomes `l₁; r₁; l₂; r₂`, WhyRel's order. A
  sequence of two bicommands is therefore *not* the same Core as one bicommand
  holding both statements per side — `Swap.relrl.st` writes both, as WhyRel
  does. CLAUDE.md says what breaks if the order is changed.

- **A call inside a bicommand is Core's `call`, and needed nothing new.** A
  split's sides are Core `Statement`s and a call is one, so relating two
  programs that call the same procedures in different orders works because Core
  resolves a call against the callee's `spec`. This is the reuse argument paying
  off rather than a feature that was added.

## Specs

- **Specs are scoped to the parameters and become Core's own contract.** A spec
  names what the caller can see, never a bi-local. That is what lets `requires`/
  `ensures` be Core `preconditions`/`postconditions` rather than an assume and
  an assert in the body — and only a real postcondition gives `old x` its
  meaning. A claim about a bi-local is an `Assert { R }` in the body instead,
  which is strictly more expressive: it is checked where it stands.
  `Program.lean`.

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
  emitting both into one list is the standard forall-forall encoding — sound
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
