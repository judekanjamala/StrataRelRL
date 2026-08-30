# Current state

> **Scope.** What the dialect can express today, and every way it differs from
> WhyRel. A *why* belongs in [`design.md`](design.md); a defect, with its root
> cause, in [`issues.md`](issues.md) — point at those rather than restating
> them. A gap against WhyRel is an entry here, not an issue.

**Works today**

- `.relrl.st` concrete syntax, parsed by DDM from the `#dialect RelRL`
  declaration, following WhyRel's: a `biproc` body is a `;`-terminated
  *sequence* of bicommands, and a bicommand is a split `<< c | c' >>`, a
  synchronized `|- c -|`, a `Var` declaration, or a relational
  `Assert { R }`.
- **A bicommand sequence expresses an alignment.** `<< a := 3 | b := 3 >> ;
  << b := 3 | a := 3 >> ;` says which step of the left lines up with which step
  of the right, as WhyRel's `( f | g ); ( g | f );` does. With nothing between
  the elements it lowers to the same Core as one bicommand holding both
  statements per side; an `Assert { R }` between them is what makes the
  alignment observable, since the assertion sees both sides exactly as they
  stand at that point.
- **`Var` declares bi-locals whose names differ, including one-sided ones.**
  `Var s : int | t : int ;` declares `s` in the left program and `t` in the
  right; `Var acc : int | ;` and `Var | u : int ;` declare a variable existing
  in only one of them. Nothing is initialized, and neither name is primed, so
  `s =:= t` relates them directly.
  `RelRL/Examples/BiVar.relrl.st` shows all three forms.
- **Synchronized bicommands declare bi-locals.** `|- var a : int := 0; -|` runs
  on both sides and declares the *pair* `a`/`a'` from one source name. It holds
  exactly one statement, as WhyRel's does, so declaring two bi-locals is two
  synchronized bicommands. It is the only form whose declarations outlive it, so
  it is what puts a name in scope for a later bicommand and for a spec. A
  split's own declarations stay local to that side.
- **Relational assertions**, in a two-layer language ported from RelRL's
  `rformula` — as an `Assert { R }` anywhere in the body, seeing both sides as
  they stand at that point, or as `requires`/`ensures` clauses above the body,
  Boogie-style and repeatable. `requires` is assumed on entry, so it can only
  name the file's top-level Core declarations; `ensures` is asserted on exit and
  can name bi-locals:

  ```
  biproc sum
    requires { Both (int.gt(bound, 0)) }
    ensures {
      Agree s                                      // RelRL's Agree
      /\ Both (int.gt(s, 0))                        // Rboth
      /\ <| last == 3 <]                            // Rleft
      /\ [> last == 1 |>                            // Rright
      /\ last =:= int.add(int.mul(last, 2), 1)      // Rbiequal
      /\ Agree a /\ Agree b                          // Rconn, with \/ => <=>
      /\ { ~ Agree last => { Agree s \/ Agree a } }  // Rnot, { … } to group
    }
  =
    |- var s : int := 0; -| ;
    << … | … >> ;
    Assert { Agree s } ;
  ```

  The expression layer inside is Core's, spelled as Core spells it —
  `int.add(a, b)`, `==` — because a relational expression *becomes* a Core
  expression. `RelRL/Examples/Assertions.relrl.st` exercises every form and
  passes 12/12.

  Everything is written with *source* names; priming is what "the right state"
  means, and the translator supplies it. A top-level `/\` is split into one
  proof obligation per conjunct.
- `StrataDDM.Program` → `Core.Program` translation, with source positions preserved
- SMT-backed verification via Core's unmodified pipeline
- **Projection.** `relrl project <file> --side left|right` prints the Core
  program for one side of every `biproc` alone — no priming, since nothing
  shares its scope, and no relational `ensures`, which names both sides. The
  self-composition that `verify` checks and the two projections are the same
  bicommand read three ways.
- A standalone `relrl` CLI (`verify`, `toCore`, `project`) with no `Strata-CLI`
  dependency

## Where to pick up

Ordered by cost, not by importance — correct this if the priorities are wrong.

1. **`Assume { R }`.** One grammar op and one branch in `lower_bicommand`,
   mirroring `bi_assert` with `Statement.assume`. The cheapest real addition.
2. **Reject same-name `Var` in the translator.** Currently caught by Core against
   the translated program — [`issues.md`](issues.md), "DDM has one linear typing
   context" — where the translator already has both the names and the source
   range to do better.
3. **`If e|e' then … else … end`.** Each branch is a bicommand sequence, so it
   needs the scope chain and `BodyState` handling that already exist; no new
   mechanism.
4. **`While e|e' . <guard> do … done`.** The first genuinely new mechanism:
   alignment guards and relational invariants have no counterpart yet.
5. **Biproc parameters and returns.** The largest blocker. WhyRel's
   `meth m (n:int|n:int) : (int|int)` has no equivalent, and without it there is
   no `result`, no call between biprocs, and no `bimodule` layer — and
   `requires` stays thin, since a precondition has only top-level constants to
   talk about.

Everything in [Not implemented](#not-implemented) below that is not listed here
needs a heap model first.

## Differences from WhyRel

Measured against `dnaumann/RelRL`'s `src/parser/parser.mly` and the examples
under `examples/all_all/`.

### Same construct, different spelling

| WhyRel | RelRL | Why |
|---|---|---|
| `( c \| c' )` | `<< c \| c' >>` | Preference. `(` is also Core's expression grouping, and `) ;` risked registering `);` as one token — `docs/design.md` |
| `\|_ c _\|` | `\|- c -\|` | Forced: DDM's lexer cannot tokenize `_\|` at all — `CLAUDE.md`, "Things that will bite" |
| `Var x:T \| y:T in CC` | `Var x:T \| y:T ;` | No `in CC`; a bicommand sequence is already the scope |
| `Both f` | `Both (e)` | Parens mandatory — the operand is a Core expression |

`=:=`, `Agree x`, `<| … <]`, `[> … |>`, `~ /\ \/ => <=>`, `Assert { R }` and the
placement of `requires`/`ensures` above the body all match WhyRel as written.

### The layer inside a bicommand is Core's

Statements and expressions inside a side are Core's, not WhyRel's: Core
terminates statements where WhyRel separates them (`i := 0;` against `i := 0`),
and spells operators as functions — `int.add(a, b)`, `int.gt(s, 0)` rather than
`a + b`, `s > 0`. Deliberate: matching WhyRel here means writing RelRL's own
statement grammar and translator, giving up the reuse of `Core.getProgram` the
whole design rests on. See `docs/design.md`.

### Not implemented

- **Bicommands.** `If e|e' then … else … end`, `While e|e' . <guard> do … done`,
  `Assume { R }`, `Connect x with y`. Split, synchronized, `Var` and `Assert`
  are what exist.
- **Formulas.** Quantifiers (`Rquant`), `let` (`Rlet`), named relational
  predicates and coupling relations (`Rprimitive`, `named_rformula`), and
  everything needing a heap: region-image agreement (``Agree e`f``), refperm.
- **Program structure.** No `interface` / `module` / `bimodule`, no classes,
  objects, heap or regions, no `effects` clauses. In particular a `biproc` has
  **no parameters or return values**, so WhyRel's
  `meth fact (n:int|n:int) : (int|int)` has no equivalent — there is no `result`
  and no way to call one biproc from another. That is what leaves `requires`
  thin: with no parameters, a precondition can only constrain the file's
  top-level Core declarations.
- **Forall-exists.** Only the forall-forall fragment; no `-all-exists` mode.

The heap is missing deliberately — the forall-forall examples being targeted
first do not need one.

### Where the semantics diverge

- **The same name on both sides is not expressible.** WhyRel's commonest
  declaration is `Var i:int | i:int` — one name, both programs. RelRL splits
  that case in two: `Var` covers *differing* names, and a shared name goes
  through `|- var i : T; -|`, one binding with the translator supplying the
  `i`/`i'` pair. Not fixable within DDM — [`issues.md`](issues.md), "DDM has one
  linear typing context".
- **Priming is visible.** WhyRel goes to Why3 with genuinely two-state formulas;
  RelRL lowers by self-composition, so the right side really is a set of
  variables named `a'`. One consequence reaches the surface language: `Agree x`
  is lexical and unchecked — [`issues.md`](issues.md), "`Agree x` is lexical".
- **A top-level `/\` is split** into one obligation per conjunct, for readable
  verifier output. RelRL's own, not WhyRel's.

### Tooling

WhyRel compiles to a Why3 `.mlw` file; RelRL lowers to Core and discharges with
cvc5 through Core's unmodified pipeline. `relrl project --side left|right`, which
prints one side as an ordinary unary Core program, has no WhyRel equivalent.
