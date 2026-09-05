# Current state

> **Scope.** What the dialect can express today, and every way it differs from
> WhyRel. A *why* belongs in [`design.md`](design.md); a defect, with its root
> cause, in [`issues.md`](issues.md) — point at those rather than restating
> them. A gap against WhyRel is an entry here, not an issue.

**Works today**

- `.relrl.st` concrete syntax, parsed by DDM from the `#dialect RelRL`
  declaration, following WhyRel's: a `biproc` body is a `;`-terminated sequence
  of bicommands — a split `<< c | c' >>`, a synchronized `|- c -|`, a `Var`
  declaration, or a relational `Assert { R }`.

- **Synchronized calls to a `biproc`**, WhyRel's `|_ m() _|` on a bimethod:
  `|- Call m (a, out r) | (b, out s) -| ;` uses `m`'s *relational* contract,
  unfolding neither body. That is what makes a relational spec a hypothesis and
  not only an obligation. The sides need not pass the same arguments, or the
  same number of them. `RelRL/Examples/BiCall.relrl.st`.

  One restriction: not inside `While e|e' . p|p' do`, whose one-sided steps are
  projections of its body — refused with a located error, and
  [`design.md`](design.md) argues why. Lockstep `While`, `WhileL` and `WhileR`
  take it.

- **`old x` in a spec**, for an `inout` parameter: its value on entry. RelRL's
  specs are Core pre/postconditions, so it works on either side and under `Both`.

- **Biproc parameters and returns.** Each side is a Core `Bindings`, so `out` and
  `inout` come from Core unchanged, and a `requires` can relate the two sides'
  inputs. `RelRL/Examples/Params.relrl.st`.

- `StrataDDM.Program` → `Core.Program` translation, source positions preserved,
  SMT-backed verification through Core's unmodified pipeline.

- **Projection.** `relrl project <file> --side left|right` prints one side of
  every `biproc` alone — no priming, since nothing shares its scope, and no
  relational `ensures`, which names both sides. The composed program and the two
  projections are the same bicommand read three ways.

- A standalone `relrl` CLI (`verify`, `toCore`, `project`), no `Strata-CLI`
  dependency.

- **Every heap-free `all_all` case study of WhyRel's**, under
  `RelRL/Examples/WhyRel/`: `factorial`, `equiv-check`, `monofact`,
  `majorization`, `Veracity/Simple_IO`, and both halves of `Veracity/Fizzbuzz`.
  Where WhyRel keeps mutable state in a module global, the port passes it
  `inout`, which is also what gives each side its own copy.

- **`Let`**, WhyRel's `Rlet`: `Let x = [< e <], y = [> e' >] :: R` names a value
  from either program. The *only* form reaching across the two at an arbitrary
  type, and the only one saying more than `=:=` — an inequality, or arithmetic
  mixing the sides. Every Core expression is in reach, since the names are bound
  variables, which nothing primes; a binding may read an earlier one, from either
  side. `monofact` and `majorization` need it; [`design.md`](design.md) records
  the two narrower forms that came before.

- **Relational quantifiers**, WhyRel's `Rquant`: `Forall xs | ys :: R` binds one
  list per side, `Forall xs |` and `Forall | ys` one side alone, and
  `Forall xs :: R` one list both readings share. `Exists` likewise. A binder is
  not program state, so nothing about it is primed — and `Forall i | i` is
  refused with a located error, since DDM would resolve every use to the inner
  binder.

## Differences from WhyRel

Measured against `dnaumann/RelRL`'s `src/parser/parser.mly` and the examples
under `examples/all_all/`.

### Same construct, different spelling

| WhyRel | RelRL | Why |
|---|---|---|
| `( c \| c' )` | `<< c \| c' >>` | Preference. `(` is also Core's expression grouping, and `) ;` risked registering `);` as one token — [`design.md`](design.md) |
| `\|_ c _\|` | `\|- c -\|` | Forced: DDM's lexer cannot tokenize `_\|` at all — [`design.md`](design.md) |
| `Var x:T \| y:T in CC` | `Var x:T \| y:T ;` | No `in CC`; a bicommand sequence is already the scope |
| `Both f` | `Both (e)` | Parens mandatory — the operand is a Core expression |
| `While e\|e' . do … done` | `While e\|e' do … done` | Lockstep is its own op rather than an empty alignment guard; DDM has no optional-with-separator form |
| `meth m (n:int\|n:int) : (int\|int)` | `biproc m (n : int, out result : int) \| (…)` | Each side is a Core `Bindings`, so `out`/`inout` and `translateProcBindings` are reused; the return is a named `out`, which is what a translator can bind |
| `\|_ m() _\|` | `\|- Call m (a, out r) \| (b, out s) -\| ;` | Arguments come per side, as the declaration's do; `Call` because after `\|- ` a Core call statement is already a live alternative — [`design.md`](design.md) |
| `[< e <] > [> e' >]` | `Let a = [< e <], b = [> e' >] :: <\| int.gt(a, b) <]` | No `biexp` grammar: naming each side covers every type instead of `int` alone — [`design.md`](design.md) |
| `let x \| y = ex \| ey in R` | `Let x = [< ex <], y = [> ey >] :: R` | Each binding carries its own side marker rather than the sides being two groups, so the list is n-ary and a one-sided `let` is one element |
| `forall xs \| ys . R` | `Forall xs \| ys :: R` | Capitalized, since a lowercase `forall` also starts a Core expression; `::` because after a type a `.` reads as a qualified name — [`design.md`](design.md) |

`result` is not a keyword: it is whatever the `out` binding is called. Naming it
`result` on both sides recovers WhyRel's spelling, and `Agree result` then means
what it does there.

`=:=`, `Agree e`, `<| … <]`, `[> … |>`, `~ /\ \/ => <=>`, `Assert { R }` and the
placement of `requires`/`ensures` above the body all match WhyRel as written.

### The layer inside a bicommand is Core's

Statements and expressions inside a side are Core's: it terminates statements
where WhyRel separates them (`i := 0;` against `i := 0`), and spells operators as
functions — `int.add(a, b)`, not `a + b`. Deliberate; matching WhyRel here means
owning a statement grammar and translator, giving up the reuse of
`Core.getProgram` the whole design rests on. [`design.md`](design.md).

One Core statement is not accepted there: a `var`. `Var` is the only form that
declares, matching WhyRel, whose `|_ … _|` takes an `atomic_command`. A `var`
anywhere inside a `|- … -|` or a split's side — nested in an `if` or `while`
body included — is refused against its own source range. Nesting is refused too
because it is not merely redundant: [`issues.md`](issues.md), "Sibling blocks
sharing a declared name lose every obligation".

### Not implemented

- **Give each program its own globals.** A top-level declaration is one symbol
  both sides read, so agreement on anything derived from it is free. A defect,
  not a divergence — [`issues.md`](issues.md) has the two routes and the
  declaration kinds affected.
- **A heap model**, deliberately: the forall-forall examples targeted first need
  none, and the heap-free fragment is complete, from `Var` through the loop
  bicommands to parameters and calls. Most of what follows does need one —
  `Connect`, loop `effects`, region-image agreement, refperm, classes, objects.
  Laurel's `HeapParameterization` is the reference: a `Heap` datatype over Core's
  own `Map`, threaded as a parameter.
- **Bicommands.** `Connect x with y` (WhyRel's `Biupdate`) and `HavocR x { R }`
  (all-exists only). Everything else WhyRel's parser accepts is implemented:
  split, synchronized, synchronized `Call`, `Var`, `Assert`, `Assume`, `If`,
  `If4`, `While`, `WhileL`, `WhileR`.
- **Loop `effects` and `variant`.** `effects` needs regions; `variant` measures
  the right side and is not needed for forall-forall, so it is omitted rather
  than deferred.
- **Datatypes and multi-function `rec` blocks alongside a `biproc`.** Refused by
  `misaligning_command?` in `Translate/Program.lean` — the body's references
  would resolve against a short binding list ([`issues.md`](issues.md)). Either
  is fine in a file with no `biproc`; so are type synonyms, opaque `type`s and
  single-function `rec` blocks alongside one. The fix is upstream, and not
  urgent: the guard refuses the combination rather than mistranslating it.
- **Formulas.** Named relational predicates and coupling relations
  (`Rprimitive`, `named_rformula`), and everything needing a heap: region-image
  agreement (``Agree e`f``), refperm.
- **Program structure.** No `interface`/`module`/`bimodule`, no classes, objects
  or regions. A relational spec is already usable as a hypothesis; what a
  `bimodule` would add is the module structure itself, and the per-side unary
  specs that would let a synchronized `Call` survive projection.
- **Forall-exists.** Only the forall-forall fragment; no `-all-exists` mode.

### Where the semantics diverge

- **Priming is visible.** WhyRel goes to Why3 with genuinely two-state formulas;
  RelRL composes the two into one, so the right side is variables named `a'` —
  the prime convention, not `l_`/`r_` prefixes — and *every* name a right-hand
  fragment mentions is renamed, which keeps a one-sided variable from being
  shared. None of it reaches the surface: the primed name is never written, so
  `Agree e` is just `e =:= e` ([`design.md`](design.md)).
- **A top-level `/\` is split** into one obligation per conjunct, and a top-level
  `Both (e)` into one per program, for readable output. RelRL's own.
