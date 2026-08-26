# Design decisions

- **Own package, own CLI.** The repo split follows Strata's
  `docs/verso/IRTranslationPhilosophyDoc.lean` ("Relation to the proposed
  repository split", issue #1168): a dialect plus its translation-to-Core
  depends on `Strata`, never the reverse. The self-contained `lean_exe relrl`
  extends that to tooling — wiring RelRL into `Strata-CLI` was attempted
  first and abandoned after it spread the `Strata.Core`/`Core` namespace
  ambiguity into another repo's build.

- **Bicommand Syntactic category**

The DDM elaborator always parses category `Init.Command` at a program's top
level — hardcoded at `StrataDDM/Elab/Core.lean:1838`. So anything appearing at
top level must be an op returning `Command`, and a category nothing reaches is
simply dead: declaring `category Bicommand` and `op biembed` alone leaves
`biembed` unparseable.

An identity injection `op … (b : Bicommand) : Command => b` admits
nesting: it makes every bicommand usable as a command, so with `Command`-typed
sides `( ( a | b ) | c )` parses.

Instead `biproc` is the added as the only RelRL operator in Init's `Command`
category, and a `Bicommand` appears only as its `body` field.  Operators of
`Bicommand` take Core `Block` and no Core operator takes a `Command` as an
argument. So a side can hold only statements, a statement can never be a
`biproc`, and a `Bicommand` can never occur inside a `Bicommand`. Both forms
are rejected by the parser:

- **Hand-walk the DDM AST; don't use `ofAst`.** `#strata_gen` produces a
  typed Lean AST and an `ofAst` conversion, but no dialect in Strata
  actually translates through it — Core, C_Simp, and Laurel all walk `Operation`/`Arg` by hand.
  Following that practice is what makes reusing `Core.getProgram` possible
  instead of re-implementing per-statement translation.


- **Translate to Core, not to Imperative + Lambda.** All Strata analysis and
  verification runs on the internal Lambda/Imperative ASTs, but Core is the
  supported entry point that already wires up VC generation and SMT discharge. A
  new dialect should lower to `Core.Program` and inherit that pipeline rather
  than hooking up a verifier itself. This decoupling mirrors how `laurelToCore`
    separates Laurel translation from Core verification.

- **Relational specs relate identifiers, and the sides are flattened.** An
  `ensures [l]: a == a'` clause needs to name both sides at once, and Core block
  scoping makes that impossible while the sides are nested in `left:` / `right:`
  blocks. So translation renames each side's top-level locals apart and
  concatenates the sides — self-composition, sound for forall-forall because
  renaming makes the sides unable to observe each other. Core supplies the
  renaming (`Block.substFvar` for reads, `Block.renameLhs` for targets), so no
  new traversal was written.

- **The renaming is the prime convention, not `left_`/`right_` prefixes.** The
  left side keeps its source names and the right side's top-level locals are
  primed (`a` / `a'`), matching how relational program logics — WhyRel and the
  region-logic papers this ports from — write the two states. It also keeps the
  common case unmarked: a spec that mentions the left side reads as the original
  program. The DDM lexer already admits `'` as an identifier character
  (`StrataDDM/Parser.lean`), and Core carries the name through to SMT unchanged,
  so nothing downstream needed a new escape.

  The operands are `Ident` rather than `bool` because DDM resolves names during
  elaboration, which finishes before translation starts — so `a'`, a name
  translation invents, cannot be elaborated as an expression. See
  `docs/issues.md` for what widening this would take.
