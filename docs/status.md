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
  of the right, as WhyRel's `( f | g ); ( g | f );` does. Lowering interleaves
  per element — `(l₁|r₁); (l₂|r₂)` becomes `l₁; r₁; l₂; r₂` — so a sequence of
  two bicommands is *not* the same Core as one bicommand holding both statements
  per side. `RelRL/Examples/Swap.relrl.st` writes both, as WhyRel does. An
  `Assert { R }` between the elements is what makes an alignment observable in
  the obligations, since the assertion sees both sides exactly as they stand at
  that point.
- **`Var` declares bi-locals, one side at a time.** `Var s : int | t : int ;`
  declares `s` in the left program and `t` in the right; `Var acc : int | ;` and
  `Var | u : int ;` declare a variable existing in only one of them. Nothing is
  initialized. The names need not differ — `Var n : int | n : int ;` is WhyRel's
  own spelling and works, since the right side is primed like any other.
  `RelRL/Examples/BiVar.relrl.st` shows all three, repeated name included.
- **The prime says which program a name belongs to, everywhere.** Every
  right-side name is `x'` in the translated Core, whether it came from a
  synchronized bicommand, a split's own declaration, or a one-sided `Var`. So
  `s =:= t` reads as `s == t'`, and a colliding declaration is reported against
  its own source range rather than by Core against the fused program.
- **Unary calls inside a bicommand.** A side of a split, or a synchronized
  bicommand, may `call` a Core `procedure` declared in the same file. The call
  site uses the callee's `spec`, not its body, so two programs calling the same
  commuting methods in opposite orders relate through those specs alone — which
  is what WhyRel's flagship `all_all/swap` example does.
  `RelRL/Examples/Swap.relrl.st` ports it, `m` and `m2` both.
- **`old x` in a spec**, for an `inout` parameter: its value on entry. Core
  snapshots that for `inout` parameters, and RelRL's specs are Core
  pre/postconditions, so it works on either side and under `Both`.
- **Biproc parameters and returns.** `biproc m (n : int, out result : int) |
  (n : int, out result : int)` gives the Core procedure inputs `n`, `n'` and
  outputs `result`, `result'`. Each side is a Core `Bindings`, so `out` and
  `inout` come from Core unchanged. This is what makes `requires` mean
  something: a precondition can relate the two sides' inputs.
  `RelRL/Examples/Params.relrl.st`.
- **Conditionals.** `If e|e' then CC else DD end` and its else-less form put
  both sides under one Core `if`, which is sound because the guards are proved
  to agree first — that obligation is the point of the form. `If4 e|e'` is for
  guards that need not agree: no obligation, a branch per combination.
  `RelRL/Examples/Branching.relrl.st`.
- **Loops, with alignment guards.** `While e|e' . p|p' do invariant { R } … done`
  is WhyRel's general biwhile: `p` lets the left step alone, `p'` the right,
  neither is lockstep, and the loop carries an `align` invariant ruling out a
  state where neither may step. `While e|e' do … done` is lockstep, and
  `WhileL e` / `WhileR e` drive the loop from one side.
  `RelRL/Examples/Loops.relrl.st`.
- **`Assume { R }`**, the dual of `Assert { R }`, lowering to Core's `assume`.
- **Synchronized bicommands declare bi-locals.** `|- var a : int := 0; -|` runs
  on both sides and declares the *pair* `a`/`a'` from one source name. It holds
  exactly one statement, as WhyRel's does, so declaring two bi-locals is two
  synchronized bicommands. What is distinctive is the *pair* from one name:
  `Var` and a split's own `var` declarations outlive their bicommand too, and
  are equally nameable by a later bicommand. No spec can name any of them.
- **Relational assertions**, in a two-layer language ported from RelRL's
  `rformula` — as an `Assert { R }` anywhere in the body, seeing both sides as
  they stand at that point, or as `requires`/`ensures` clauses above the body,
  Boogie-style and repeatable. Both spec clauses are scoped to the parameters,
  so they name what the caller can see and never a bi-local, and both become
  Core's own pre/postconditions — which is what makes `old x` mean the entry
  value of an `inout` parameter. A claim about a bi-local is an `Assert`:

  ```
  biproc sum
    requires { Both (int.gt(bound, 0)) }   // `bound` is top-level, so nameable
  =
    |- var s : int := 0; -| ;
    << … | … >> ;
    Assert {
      Agree s                                      // RelRL's Agree
      /\ Both (int.gt(s, 0))                        // Rboth
      /\ <| last == 3 <]                            // Rleft
      /\ [> last == 1 |>                            // Rright
      /\ last =:= int.add(int.mul(last, 2), 1)      // Rbiequal
      /\ Agree a /\ Agree b                          // Rconn, with \/ => <=>
      /\ { ~ Agree last => { Agree s \/ Agree a } }  // Rnot, { … } to group
    } ;
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

**A heap model is the next thing.** Everything in
[Not implemented](#not-implemented) below needs one, and nothing above it does:
the forall-forall fragment without a heap is complete, from `Var` through the
loop bicommands to parameters and unary calls.

One loose end, not urgent: the `datatype` misalignment
([`issues.md`](issues.md)) is contained by a guard rather than fixed. Fixing it
upstream would let `misaligning_command?` be deleted.

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
| `While e\|e' . do … done` | `While e\|e' do … done` | Lockstep is its own op rather than an empty alignment guard; DDM has no optional-with-separator form |
| `meth m (n:int\|n:int) : (int\|int)` | `biproc m (n : int, out result : int) \| (n : int, out result : int)` | Each side is a Core `Bindings`, so `out`/`inout` and `translateProcBindings` are reused; the return is a named `out` rather than an implicit `result`, which a translator cannot bind into DDM's elaborator |

`result` is not a keyword: it is whatever the `out` binding is called. Naming it
`result` on both sides recovers WhyRel's spelling, and `Agree result` then means
what it does there.

`=:=`, `Agree x`, `<| … <]`, `[> … |>`, `~ /\ \/ => <=>`, `Assert { R }` and the
placement of `requires`/`ensures` above the body all match WhyRel as written.

### The layer inside a bicommand is Core's

Statements and expressions inside a side are Core's, not WhyRel's: Core
terminates statements where WhyRel separates them (`i := 0;` against `i := 0`),
and spells operators as functions — `int.add(a, b)`, `int.gt(s, 0)` rather than
`a + b`, `s > 0`. Deliberate: matching WhyRel here means writing RelRL's own
statement grammar and translator, giving up the reuse of `Core.getProgram` the
whole design rests on. See `docs/design.md`.

### Other

- **The renaming is the prime convention, not `left_`/`right_` prefixes.** 


### Not implemented

- **Bicommands.** `Connect x with y` (WhyRel's `Biupdate`, which updates a
  refperm) and `HavocR x { R }` (all-exists mode only). Everything else WhyRel's
  parser accepts is implemented: split, synchronized, `Var`, `Assert`, `Assume`,
  `If`, `If4`, `While`, `WhileL`, `WhileR`.
- **Loop `effects` and `variant`.** WhyRel's `biwhile_spec` carries both.
  `effects` needs regions. `variant` measures the right side, and is not needed
  for the forall-forall fragment RelRL targets, so it is omitted rather than
  deferred.
- **Datatypes and multi-function `rec` blocks alongside a `biproc`.** Rejected
  with a located error: the biproc body's references to top-level declarations
  would resolve against a short binding list — [`issues.md`](issues.md), "A
  `datatype` breaks the top-level binding list". Either is fine in a file with
  no `biproc`; so are type synonyms, opaque `type`s and single-function `rec`
  blocks alongside one.
- **Formulas.** Quantifiers (`Rquant`), `let` (`Rlet`), named relational
  predicates and coupling relations (`Rprimitive`, `named_rformula`), and
  everything needing a heap: region-image agreement (``Agree e`f``), refperm.
- **Program structure.** No `interface` / `module` / `bimodule`, no classes,
  objects, heap or regions, no `effects` clauses. Parameters, returns and unary
  calls all exist; what a `bimodule` would add on top is the module structure
  itself, and the relational specs that go with it.
- **Forall-exists.** Only the forall-forall fragment; no `-all-exists` mode.

The heap is missing deliberately — the forall-forall examples being targeted
first do not need one.

### Where the semantics diverge

- **Priming is visible.** WhyRel goes to Why3 with genuinely two-state formulas;
  RelRL lowers by self-composition, so the right side really is a set of
  variables named `a'`, and *every* name a right-hand fragment mentions is
  renamed — which is what keeps a one-sided variable from being shared. Two
  consequence reaches the surface language: `Agree x` takes an `Ident` rather
  than an expression, since `x'` is a name lowering invents and DDM has nothing
  to elaborate it against — `docs/design.md`. The translator checks that operand,
  and every other name a side mentions, against what that side declared.
- **A top-level `/\` is split** into one obligation per conjunct, for readable
  verifier output. RelRL's own, not WhyRel's.

### Tooling

WhyRel compiles to a Why3 `.mlw` file; RelRL lowers to Core and discharges with
cvc5 through Core's unmodified pipeline. 