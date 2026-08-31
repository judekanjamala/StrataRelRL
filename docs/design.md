# Design decisions

> **Scope.** One bullet per decision: what was chosen, what was rejected, and
> why. No usage, no status, no defect lists — [`status.md`](status.md) says what
> exists, [`issues.md`](issues.md) what is broken, `CLAUDE.md` what bites when
> editing.

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
simply dead: declaring `category Bicommand` and `op bi_embed` alone leaves
`bi_embed` unparseable.

An identity injection `op … (b : Bicommand) : Command => b` admits
nesting: it makes every bicommand usable as a command, so with `Command`-typed
sides `( ( a | b ) | c )` parses.

Instead `biproc` is the added as the only RelRL operator in Init's `Command`
category, and a `Bicommand` appears only inside its `body` field, as an element
of a sequence.  Operators of
`Bicommand` take Core `Statement`s and no Core operator takes a `Command` as an
argument. So a side can hold only statements, a statement can never be a
`biproc`, and a `Bicommand` can never occur inside a `Bicommand`. Both forms
are rejected by the parser:

- **The surface syntax follows WhyRel, the expression layer does not.** From
  `dnaumann/RelRL` (`src/parser/parser.mly`, `examples/all_all/factorial/prog.rl`):
  a biprogram is a `;`-terminated sequence of bicommands; a bicommand is a split
  `( c | c' )`, a synchronized `|_ c _|`, or a relational `Assert { R }`; and a
  relational formula is built from `Agree x`, `Both (e)`, the one-sided
  projections `<| e <]` / `[> e |>`, `l =:= r`, and `~ /\ \/ => <=>`.

  Three deliberate deviations:

  1. **Statements inside a side are Core's, not WhyRel's.** Core terminates
     statements (`i := 0;`) where WhyRel separates them (`i := 0`), and its
     expressions are `int.add(a, b)` rather than `a + b`. Matching WhyRel there
     means writing RelRL's own statement grammar and translating it, which
     gives up the whole point of reusing `Core.getProgram`.
  2. **The synchronized bicommand closes with `-|`, not `_|`.** Forced: DDM's
     lexer cannot tokenize `_|` at all. CLAUDE.md, "Things that will bite", has
     the mechanism.
  3. **The split is `<< c | c' >>`, not `( c | c' )`.** A house preference —
     parentheses parsed fine — but `<<`/`>>` are unmistakably a bicommand where
     `(` is also Core's expression grouping, and it sidesteps the `);` token
     trap CLAUDE.md records. Core has no infix `>`, so `>>` cannot collide with
     an expression.

- **Two declaration forms, split by what they declare, not by how they name.**
  `Var x : T | y : T ;` declares one variable per side, each under its own name,
  with either side omittable so a variable can exist in only one program. It is
  WhyRel's `Var x:T | y:T in CC` without the `in CC`, since a bicommand sequence
  is already the scope. Nothing is initialized.

  The names need not differ: the right side is primed, so `Var i:int | i:int ;`
  — what WhyRel writes most often — lowers to `i` and `i'` like any other pair.
  DDM's single linear typing context does end up holding two bindings called
  `i`, and cannot tell them apart by which side of the `|` a reference sits on,
  but it never has to: priming is applied by syntactic side, after elaboration,
  so a right-hand fragment is renamed whichever binding its `i` resolved to.

  What separates the forms is not scope — both carry `@[scope(…)]`, so both
  outlive their bicommand — but what they declare. `Var` declares two variables
  that happen to be written together, each nameable only from its own side.
  `|- var i : T; -| ;` declares *one* thing: a bi-local, one statement run by
  both programs, whose two Core variables the translator supplies from a single
  source name. Only the second gives a name that `Agree i` and `Both (p)` can
  read, since only it asserts that both programs have this variable.

- **`|- … -|` declares a bi-local, and a spec can name what outlives the body.**
  A synchronized bicommand holds one statement — WhyRel's is
  `LEFT_SYNC atomic_command RIGHT_SYNC` — and carries `@[scope(c)]`, so its
  declarations outlive it and reach both later bicommands and the `ensures`
  clause (which carries `@[scope(body)]`); `Var` does the same through
  `@[scope(l)]`/`@[scope(r)]`. What is distinctive is the lowering: the one
  statement is lowered once and emitted twice — unprimed on the left, primed on
  the right — so `|- var a : int := 0; -|` declares the *pair* `a`/`a'` from one
  source name.

  A `bi_embed` side's own declarations stay local to that side: the grammar
  exports nothing from a split, so both sides may reuse a name, and a later
  bicommand or a spec cannot see either copy. `docs/issues.md` records what
  that costs.

- **Relational formulas lower to Core `bool`, and a top-level `/\` splits.**
  Priming is what "the right state" means: a right-hand fragment has every
  variable it mentions renamed to its primed copy — the variable the right
  side's statements were lowered onto. So `Both (e)` is `e && prime e`, and
  `l =:= r` is `l == prime r`. Connectives become Core's own operators via
  `Core.boolAndOp` and friends, the same values `translateFnTable` maps Core's
  surface syntax onto.

  A top-level conjunction is peeled into one `assert` per conjunct
  (`top_conjuncts`), because one obligation per conjunct reads far better in the
  verifier's output than a single opaque `&&`. `{ … }` is transparent to that
  peeling; every other connective is opaque, since its parts are not separately
  provable.

- **A bicommand sequence is an alignment, and lowering flushes at each
  assertion.** WhyRel writes two commuting calls as `( f | g ); ( g | f );` —
  a sequence of bicommands, one per aligned step — rather than one bicommand
  holding two sequences per side. RelRL keeps that, so `<< a := 3 | b := 3 >> ;
  << b := 3 | a := 3 >> ;` says *which* step lines up with which.

  Lowering emits every pending left side and then every pending right side,
  which for a sequence with nothing between its elements is the same Core as one
  bicommand holding the same statements — byte for byte. That is correct rather
  than lossy: priming leaves the sides unable to observe each other, so how the
  pairs interleave is unobservable, and self-composition proper is the whole
  left program followed by the whole right one.

  What makes an alignment *observable* is a relational assertion between the
  elements. `BodyState.flush` empties the pending statements at each
  `Assert { R }`, so the formula sees both sides as they stand at exactly that
  point:

  ```
  << a := 3 | b := 3 >> ;
  Assert { Agree a } ;      // fails: a = 3, a' = 0
  << b := 3 | a := 3 >> ;
  ```

  lowers to `a := 3; b' := 3; assert a == a'; b := 3; a' := 3;` — the assert
  lands between the two aligned steps, not after both. The same `Agree a` in the
  `ensures` passes, which is exactly the alignment being observable.

- **Specs sit above the body, and the two clauses differ in scope.** Boogie and
  WhyRel both write `requires`/`ensures` between the signature and the body, and
  both allow repeats, so RelRL does too. What matters is that they are not
  symmetric:

  `requires` is assumed on entry, when the body has declared nothing, so it
  carries no `@[scope(…)]` and elaborates in the biproc's incoming scope — the
  file's top-level Core declarations. Naming a bi-local in it is a scope error,
  correctly: the variable does not exist yet. `ensures` is asserted on exit, so
  it carries `@[scope(body)]` and can name bi-locals.

  `ens` is declared *after* `body` in the operator's argument list so that
  `@[scope(body)]` can refer back to it, while the syntax still prints and
  parses it before the body. DDM elaborates arguments in declaration order and
  the syntax string may reference them in any order, so the two are free to
  disagree.

- **Top-level Core commands are translated in one pass, not one at a time.** A
  `.fvar i` in Core's AST is an index into the program's top-level declarations,
  and `TransBindings.freeVars` is what it indexes. Translating each command in
  its own singleton program — which is what translation used to do — left that
  array empty, so every cross-reference silently resolved to declaration 0:
  `axiom [p]: int.gt(bound, 0)` came out as `int.gt(0, 0)`. That is a *false*
  axiom, which makes every obligation in the file vacuously provable, so the
  bug was worse than a wrong answer. The Core commands now go through one
  `translateCoreDecls` call and the biprocs are lowered against the bindings it
  produces. A `biproc` declares no top-level name, so filtering the bicommands
  out of that pass keeps the indices aligned.

- **Lowering runs inside Core's `TransM`, threading `TransBindings`.** Each side
  used to be translated as its own singleton `StrataDDM.Program`. That cannot
  survive a shared elaboration scope: a reference resolved against an enclosing
  context carries a de Bruijn index that means nothing in a fresh program, and
  Core aborts with `translateExpr out-of-range bound variable` after silently
  miscompiling (`b := a` became `b := 0` when this was first tried). `TransM`,
  `TransBindings`, `translateStmt` and `translateBlock` are all public
  (`Strata/Languages/Core/DDMTransform/Translate.lean:22`), and `translateBlock`
  takes bindings in and hands them back, so the translator now threads that
  state along exactly the chain the grammar's `@[scope(…)]` annotations
  describe. The two must be kept in step by hand.

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

- **Relational specs name both sides, and the sides are flattened.** An
  `ensures [l]: a == a'` clause needs to name both sides at once, and Core block
  scoping makes that impossible while the sides are nested in `left:` / `right:`
  blocks. So translation renames the right side apart and concatenates the
  sides — self-composition, sound for forall-forall because renaming makes the
  sides unable to observe each other. That soundness needs the rename to be
  *total* over the fragment, which is why it is driven by what the fragment
  mentions rather than by a list of expected names; CLAUDE.md's second invariant
  says what happens otherwise. Core supplies the renaming itself
  (`Block.substFvar` for reads, `Block.renameLhs` for targets), so no new
  traversal was written.

- **The renaming is the prime convention, not `left_`/`right_` prefixes.** The
  left side keeps its source names and every right-side variable is primed
  (`a` / `a'`), matching how relational program logics — WhyRel and the
  region-logic papers this ports from — write the two states. It also keeps the
  common case unmarked: a spec that mentions the left side reads as the original
  program. The DDM lexer already admits `'` as an identifier character
  (`StrataDDM/Parser.lean`), and Core carries the name through to SMT unchanged,
  so nothing downstream needed a new escape.

- **The assertion language is RelRL's own category, not Core's `Expr`.** A
  spec's operands cannot be Core expressions: DDM resolves names during
  elaboration, which finishes before translation starts, so `a'` — a name
  translation invents — fails there with `Unknown expr identifier a'`. The
  original grammar dodged this by making an agreement two `Ident`s, which are
  lexical and need no resolution, at the price that `a == a' + 1` did not parse.

  `RelExpr` generalises the dodge instead of living with it. It is RelRL's own
  expression category, and its leaves are `Ident` and `Num`, so an expression
  in a spec is never resolved either — the translator walks it and builds the
  `Core.Expression.Expr` itself, exactly as the old two-identifier agreement
  built its `.eq`. That is what makes the rest of RelRL's `rformula` reachable:
  `Both`, `Agree`, `<| … <]`, `[> … |>` and the connectives are all just shapes
  over expressions. What is left of the old limitation is that nothing checks a
  spec's names until Core does; see `docs/issues.md`.

- **Two layers, and no token shared between them.** RelRL separates a one-state
  `formula` from a two-state `rformula`, and spells them differently: `&&`,
  `||`, `not` in an expression, `/\`, `\/`, `~`, `->`, `<->` in a relational
  formula. `RelExpr`/`RelFormula` keep that split, so the parser never has to
  decide which layer a `(`-less operator belongs to, and a reader never has to
  either.

  Within `RelExpr` the spelling is Core's, not RelRL's: `int.add(a, b)` and
  `int.lt(i, n)` rather than `a + b` and `i < n`, with Core's precedences for
  `==`, `&&`, `==>`. A `RelExpr` *becomes* a Core expression, and the same text
  appears in the statements on either side of the `|`, so having it group one
  way in a `while` guard and another in an `ensures` would be a trap. Core has
  no infix arithmetic; neither does this.

  Grouping in a relational formula is `{ … }`, not `( … )`. `Both (e)` already
  spends `( … )` on a Core expression, and a formula's operands are Core
  expressions throughout, so `( … )` in formula position would be ambiguous.
  RelRL brackets a whole assertion the same way — `ensures { … }`.

- **Every relational form is written with source names; the translator primes.**
  `Both (i == n)` lowers to `i == n && i' == n'` — `prime_expr` applies to the
  expression exactly the substitution `prime_stmts` applies to the right side's
  statements, from the same bi-local set. No form makes the user write a prime:
  where the two sides genuinely differ, `l =:= r` relates a left expression to a
  right one (`last =:= int.add(int.mul(last, 2), 1)` is `last == 2 * last' + 1`),
  which is WhyRel's spelling and keeps `'` out of the surface syntax entirely.
