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

- **Synchronized calls to a `biproc`**, WhyRel's `|_ m() _|` on a bimethod:
  `|- Call m (a, out r) | (b, out s) -| ;` calls `m` with the left side's
  arguments and the right side's, and the call site uses `m`'s *relational*
  contract — neither body is unfolded. This is what makes a `biproc`'s spec a
  hypothesis and not only an obligation, and so what makes relational reasoning
  modular. The two sides need not pass the same arguments or the same number of
  them; only `m`'s `requires` has to hold of the pair.
  `RelRL/Examples/BiCall.relrl.st`.

  One restriction: not inside `While e|e' . p|p' do`. That form's one-sided
  steps are projections of its body, and a `biproc` has no unary contract to
  call there — refused with a located error, `docs/design.md` argues why. The
  lockstep `While`, `WhileL` and `WhileR` take it.

- **`old x` in a spec**, for an `inout` parameter: its value on entry. Core
  snapshots that for `inout` parameters, and RelRL's specs are Core
  pre/postconditions, so it works on either side and under `Both`.
- **Biproc parameters and returns.** `biproc m (n : int, out result : int) |
  (n : int, out result : int)` gives the Core procedure inputs `n`, `n'` and
  outputs `result`, `result'`. Each side is a Core `Bindings`, so `out` and
  `inout` come from Core unchanged. This is what makes `requires` mean
  something: a precondition can relate the two sides' inputs.
  `RelRL/Examples/Params.relrl.st`.

- `StrataDDM.Program` → `Core.Program` translation, with source positions
  preserved and SMT-backed verification via Core's unmodified pipeline
- **Projection.** `relrl project <file> --side left|right` prints the Core
  program for one side of every `biproc` alone — no priming, since nothing
  shares its scope, and no relational `ensures`, which names both sides. The
  composed program that `verify` checks and the two projections are the same
  bicommand read three ways.
- A standalone `relrl` CLI (`verify`, `toCore`, `project`) with no `Strata-CLI`
  dependency
- **Every heap-free `all_all` case study of WhyRel's**, under
  `RelRL/Examples/WhyRel/`: `factorial`, `equiv-check`, `monofact`,
  `majorization`, `Veracity/Simple_IO`, and both halves of
  `Veracity/Fizzbuzz`. Where WhyRel keeps mutable state in a module global, the
  port passes it `inout` instead, which is also what gives each side its own
  copy.

- **`Let`**, WhyRel's `Rlet`: `Let x = [< e <], y = [> e' >] :: R` names a value
  from either program and says what it likes about the names. This is what puts
  *every* Core expression across the two programs — `bool`, `real`, `Map`,
  `Sequence`, a user `function`, any type at all — since the body is an ordinary
  relational formula and the names are Core bound variables, which nothing
  primes. A binding may also read what an earlier one declared, from either
  side. `BiExp` below stays the `int` shorthand rather than growing a copy of
  Core's operator grammar; `docs/design.md` argues why that split.

- **Cross-side comparison and arithmetic**, WhyRel's `biexp`. `[< e <]` reads
  the left state and `[> e >]` the right, Core's own int operators combine
  them — so one term may mix the two, `int.add([< i <], [> j >])` — and
  `Rel int.gt (l, r)` compares two of them. `Rel int.gt (l | r)` is the
  whole-value case, where position picks the side as in `l =:= r`; it is sugar
  for `Rel int.gt ([< l <], [> r >])`. A constant is `[< 1 <]`, a literal
  reading the same in either state, rather than WhyRel's `[1]`.
  `monofact` and `majorization` are what need the form.

- **Relational quantifiers**, WhyRel's `Rquant`: `Forall xs | ys :: R` binds one
  list per side, `Forall xs |` and `Forall | ys` one side alone, and
  `Forall xs :: R` one list both readings share. `Exists` likewise. A binder is
  not program state, so nothing about it is primed — and so `Forall i | i` is
  refused with a located error, since DDM would resolve every use to the inner
  binder and leave the outer one unreachable.

## Differences from WhyRel

Measured against `dnaumann/RelRL`'s `src/parser/parser.mly` and the examples
under `examples/all_all/`.

### Same construct, different spelling

| WhyRel | RelRL | Why |
|---|---|---|
| `( c \| c' )` | `<< c \| c' >>` | Preference. `(` is also Core's expression grouping, and `) ;` risked registering `);` as one token — `docs/design.md` |
| `\|_ c _\|` | `\|- c -\|` | Forced: DDM's lexer cannot tokenize `_\|` at all — [`design.md`](design.md) |
| `Var x:T \| y:T in CC` | `Var x:T \| y:T ;` | No `in CC`; a bicommand sequence is already the scope |
| `Both f` | `Both (e)` | Parens mandatory — the operand is a Core expression |
| `While e\|e' . do … done` | `While e\|e' do … done` | Lockstep is its own op rather than an empty alignment guard; DDM has no optional-with-separator form |
| `meth m (n:int\|n:int) : (int\|int)` | `biproc m (n : int, out result : int) \| (n : int, out result : int)` | Each side is a Core `Bindings`, so `out`/`inout` and `translateProcBindings` are reused; the return is a named `out` rather than an implicit `result`, which a translator cannot bind into DDM's elaborator |
| `\|_ m() _\|` | `\|- Call m (a, out r) \| (b, out s) -\| ;` | The arguments come per side, as the declaration's do; `Call` rather than Core's `call` because after `\|- ` a Core call statement is already a live alternative — `docs/design.md` |
| `[< e <] > [> e' >]` | `Rel int.gt ([< e <], [> e' >])`, or `Rel int.gt (e \| e')` | Operators are Core's own functions rather than infix; the short form drops the markers where position already picks the side — `docs/design.md`. Int only |
| `let x \| y = ex \| ey in R` | `Let x = [< ex <], y = [> ey >] :: R` | Each binding carries its own side marker rather than the sides being split into two groups, so the list is n-ary and a one-sided `let` is just a one-element list |
| `forall xs \| ys . R` | `Forall xs \| ys :: R` | `Forall` capitalized, since a lowercase `forall` also starts a Core expression, which is what a `=:=` operand is; `::` because after a type a `.` reads as the start of a qualified name — `docs/design.md` |

`result` is not a keyword: it is whatever the `out` binding is called. Naming it
`result` on both sides recovers WhyRel's spelling, and `Agree result` then means
what it does there.

`=:=`, `Agree e`, `<| … <]`, `[> … |>`, `~ /\ \/ => <=>`, `Assert { R }` and the
placement of `requires`/`ensures` above the body all match WhyRel as written.

### The layer inside a bicommand is Core's

Statements and expressions inside a side are Core's, not WhyRel's: Core
terminates statements where WhyRel separates them (`i := 0;` against `i := 0`),
and spells operators as functions — `int.add(a, b)`, `int.gt(s, 0)` rather than
`a + b`, `s > 0`. Deliberate: matching WhyRel here means writing RelRL's own
statement grammar and translator, giving up the reuse of `Core.getProgram` the
whole design rests on. See `docs/design.md`.

One Core statement is not accepted there: a `var`. `Var` is the only form that
declares, matching WhyRel, whose `|_ … _|` takes an `atomic_command` and whose
only binder is `Var … in CC`. A `var` anywhere inside a `|- … -|` or a split's
side — nested in an `if` or `while` body included — is refused against its own
source range. Nesting is refused too because it is not merely redundant:
[`issues.md`](issues.md), "Sibling blocks sharing a declared name lose every
obligation".

### Other

- **The renaming is the prime convention, not `l_`/`r_` prefixes.** 


### Not implemented

- **Give each program its own globals.** A top-level declaration is currently
  one symbol both sides read, so agreement on anything derived from it is free.
  Each should get a primed copy, as every bi-local does — a defect, not a
  deliberate divergence. `Translate/Priming.lean` and `Translate/Program.lean`;
  [`issues.md`](issues.md) has the two routes and which declaration kinds are
  affected.
- **A heap model.** Most of what follows needs one — `Connect`, loop `effects`,
  region-image agreement, refperm, classes and objects. Nothing in **Works
  today** does: the forall-forall fragment without a heap is complete, from
  `Var` through the loop bicommands to parameters, unary calls and synchronized
  `biproc` calls. Missing deliberately, since the forall-forall examples being
  targeted first do not need one. Laurel's `HeapParameterization` is the
  reference — a `Heap` datatype over Core's own `Map` and datatypes, threaded
  as a parameter.
- **Bicommands.** `Connect x with y` (WhyRel's `Biupdate`, which updates a
  refperm) and `HavocR x { R }` (all-exists mode only). Everything else WhyRel's
  parser accepts is implemented: split, synchronized, synchronized `Call`,
  `Var`, `Assert`, `Assume`, `If`, `If4`, `While`, `WhileL`, `WhileR`.
- **Loop `effects` and `variant`.** WhyRel's `biwhile_spec` carries both.
  `effects` needs regions. `variant` measures the right side, and is not needed
  for the forall-forall fragment RelRL targets, so it is omitted rather than
  deferred.
- **Datatypes and multi-function `rec` blocks alongside a `biproc`.** Rejected
  with a located error by `misaligning_command?` in `Translate/Program.lean`:
  the biproc body's references to top-level declarations would resolve against a
  short binding list — [`issues.md`](issues.md), "A `datatype` breaks the
  top-level binding list". Either is fine in a file with no `biproc`; so are type
  synonyms, opaque `type`s and single-function `rec` blocks alongside one. The
  fix is upstream: have Core's `translateCoreDecls` return its final
  `TransBindings`, after which the guard can be deleted. Not urgent — the guard
  refuses the combination rather than mistranslating it.
- **Formulas.** Named relational predicates and coupling relations
  (`Rprimitive`, `named_rformula`), and everything needing a heap: region-image
  agreement (``Agree e`f``), refperm.
- **`BiExp` at a type other than `int`.** Every `BiExp` slot is `int`: the
  leaves, the operators (Core's `int` categories), and `Rel`'s comparison. Each
  violation is a located error rather than a silent mistranslation — a `bool`
  leaf is refused by DDM's own typechecker, a `bool` operator by the parser.

  This is a gap in the *shorthand*, not in what can be said: `Let` above reaches
  every type, so `Rel int.le ([< a <], [> b >])` is the terse form of something
  `Let a' = [< a <], b' = [> b >] :: <| int.le(a', b') <]` can always express.
  Widening `BiExp` is a matter of another operator category in `Grammar.lean`
  and another entry in `int_op`, if the shorthand is ever wanted at `real` or
  `bv`.
- **Program structure.** No `interface` / `module` / `bimodule`, no classes,
  objects or regions, no `effects` clauses. Parameters, returns, unary calls and
  synchronized `biproc` calls all exist, so a relational spec is already usable
  as a hypothesis; what a `bimodule` would add on top is the module structure
  itself, and the per-side unary specs that would let a synchronized `Call`
  survive projection.
- **Forall-exists.** Only the forall-forall fragment; no `-all-exists` mode.

### Where the semantics diverge

- **Priming is visible.** WhyRel goes to Why3 with genuinely two-state formulas;
  RelRL composes the two programs into one, so the right side really is a set
  of variables named `a'`, and *every* name a right-hand fragment mentions is
  renamed — which is what keeps a one-sided variable from being shared. Nothing
  of this reaches the surface language: the primed name is never written, so
  `Agree e` is just `e =:= e` and both operands elaborate in the same scope —
  `docs/design.md`. The translator checks the lowered formula, and every other
  name a side mentions, against what that side declared.
- **A top-level `/\` is split** into one obligation per conjunct, and a
  top-level `Both (e)` into one per program, for readable verifier output.
  RelRL's own, not WhyRel's.
