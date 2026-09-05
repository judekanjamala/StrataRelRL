# StrataRelRL

> **Scope.** How to work in this repo: the commands, the traps, the invariants
> to protect, and where each kind of prose belongs. Not a reference — the docs
> below are, and each states its own scope.

A Strata dialect adding **bicommands** on top of Strata Core, verified by
lowering to Core. `README.md` covers intent and the file layout;
`docs/status.md` what works and how the dialect differs from WhyRel;
`docs/workflows.md` how the workflows relate, each documented in its own module;
`docs/design.md` the decisions and why they went that way; `docs/issues.md`
known defects, each traced to its root cause.

## Commands

```console
lake build relrl
lake exe relrl verify RelRL/Examples/Assertions.relrl.st  # smoke test: expect 20/20 passed
lake exe relrl verify RelRL/Examples/SeqBi.relrl.st       # expect 5/5 passed
lake exe relrl verify RelRL/Examples/Swap.relrl.st        # expect 6/6 passed
lake exe relrl verify RelRL/Examples/BiVar.relrl.st       # expect 4/4 passed
lake exe relrl verify RelRL/Examples/Branching.relrl.st   # expect 5/5 passed
lake exe relrl verify RelRL/Examples/Loops.relrl.st       # expect 20/20 passed
lake exe relrl verify RelRL/Examples/Params.relrl.st      # expect 5/5 passed
lake exe relrl verify RelRL/Examples/BiCall.relrl.st      # expect 7/7 passed
lake exe relrl toCore RelRL/Examples/Swap.relrl.st        # print the translated Core program
lake exe relrl project RelRL/Examples/Swap.relrl.st --side left   # one side alone, as Core
```

WhyRel's case studies, under `RelRL/Examples/WhyRel/`. The last two reason about
map *equality*, so they need `--use-array-theory` — see below.

```console
lake exe relrl verify RelRL/Examples/WhyRel/Factorial.relrl.st    # expect 15/15 passed
lake exe relrl verify RelRL/Examples/WhyRel/EquivCheck.relrl.st   # expect 18/18 passed
lake exe relrl verify RelRL/Examples/WhyRel/MonoFact.relrl.st     # expect 11/11 passed
lake exe relrl verify RelRL/Examples/WhyRel/Majorization.relrl.st # expect 10/10 passed
lake exe relrl verify RelRL/Examples/WhyRel/FizzBuzzSum.relrl.st  # expect 23/23 passed
lake exe relrl verify --use-array-theory RelRL/Examples/WhyRel/FizzBuzz.relrl.st  # expect 21/21
lake exe relrl verify --use-array-theory RelRL/Examples/WhyRel/SimpleIO.relrl.st  # expect 29/29
```

`lake exe` resolves and rebuilds; prefer it over `./.lake/build/bin/relrl`.
Verification needs an SMT solver on `PATH` (cvc5 by default).

## Comments: one fact, one place

The intro above says which file owns which kind of prose. Respect it when
writing comments:

| Kind | Home |
|---|---|
| What works, and how it differs from WhyRel | `docs/status.md` |
| Why a decision went the way it did | `docs/design.md` |
| What bites when editing | this file |
| How a command or stage works | the module that implements it |
| A defect, and what fixing it takes | `docs/issues.md` |

Every doc opens with a **Scope** note repeating its half of this table. Read it
before adding to that file, and if what you are writing does not fit, put it
where it belongs and leave a pointer.

A gap against WhyRel is a `status.md` entry, not an issue. When the cause is a
Strata or translation constraint that cannot be fixed, `status.md` names it and
points at the `issues.md` section that explains it.

- **Code comments say *what*; they point for *why*.** A docstring restating an
  argument from `docs/design.md` goes stale independently of it. Two lines and a
  pointer beat a paragraph.
- **Never explain the same fact twice** — not across two files, not in a module
  docstring and again on the function. Put it where the table says and leave a
  pointer everywhere else.
- **Don't narrate the code.** Say what an argument means or why a step is
  needed, not what the next three lines do.
- **Example headers are ~3 lines**: what the file demonstrates, plus where the
  reasoning lives. `RelRL/Examples/Assertions.relrl.st` is the exception — its
  per-form annotations are the content.
- **Do comment the non-obvious mechanics**, which are what a reader cannot
  recover from the code: why a sequence is re-tagged `.newline`. Everything
  else, delete.
- When a fact moves, grep for it. Delimiters, op names and expected goal counts
  have all been restated in four places at once here.

## Things that will bite

- **A `datatype` or multi-function `rec` block in the same file as a `biproc`
  is refused**, by `misaligning_command?` in `Translate/Program.lean`. Not a style rule:
  the body's references to top-level declarations would otherwise resolve to the
  wrong decl, or to the literal `0`, and verify a false spec. Widen the guard,
  never loosen it, until the upstream fix lands — `docs/issues.md` has both.

- **The `Strata` dependency is unpinned** — `rev = "main"` in `lakefile.toml`.
  A build that breaks after `lake update` may be upstream drift rather than a
  local change. Check `git diff` before assuming it's your edit.

- **A goal about `Map` *equality* is `unknown` without `--use-array-theory`.**
  Core's SMT encoder sends `Map` to an uninterpreted sort by default
  (`Core.VerifyOptions.default` has `useArrayTheory := false`), so `select`
  and `store` work but extensionality and store-over-store do not:
  `m[i := v][i := v] == m[i := v]` does not discharge. The flag encodes `Map` as
  an SMT array instead and it does. Passing it is harmless where it is not
  needed, so reach for it the moment a map-valued `Agree` or `==` goes
  `unknown`.

- **`warningAsError = true`.** An unused variable or a shake warning fails the
  build, not just warns.

- **Two `Core` namespaces.** `Strata.Core` (the dialect) and `_root_.Core` (the
  verification IR) both exist and resolve differently depending on the enclosing
  namespace. `RelRL/Cli/Verify.lean` writes `_root_.Core.VerifyOptions`,
  `_root_.Core.VCResult` for exactly this reason. Wiring RelRL into `Strata-CLI`
  was abandoned over this; see `docs/design.md`.

- **Inside `#dialect … #end`, comments are `//`, not `--`.** A `--` comment
  yields `expected token` at that line with no hint about why.

- **DDM's tokenizer shapes the grammar, so check it before respelling a
  literal.** Which literals can be tokens at all, why every atom in
  `Grammar.lean` holds exactly one, and which characters cannot start one:
  `docs/design.md`, "## Syntax". Respelling by eye breaks a form somewhere else
  in the file — and test the change, since what looks like an ambiguity often
  is not one.

## The invariant worth protecting

In `RelRL/DDMTransform/Grammar.lean`, a bicommand's sides are sequences of Core
`Statement`, **not** `Command`, and `Bicommand` is not a `Command`:

```
op biproc (name : Ident, params : Option BiBindings,
           @[scope(params)] reqs : Seq RelRequires,
           @[scope(params)] ens : Seq RelEnsures,
           @[scope(params)] body : Seq Bicommand) : Command =>
  "biproc " name params reqs ens " =\n  " indent(2, body);
op bi_embed (left : NewlineSepBy Statement,
             right : NewlineSepBy Statement) : Bicommand =>
  "<<\n  " indent(2, left) "\n|\n  " indent(2, right) "\n>>" " ;";
```

No Core `Statement`/`Block` operator takes a `Command`, so a `Bicommand` cannot
recur through its own sides. Making the sides `Command`, or adding
`op inj (b : Bicommand) : Command => b`, reintroduces nesting immediately —
`<< << a | b >> | c >>` starts parsing. `docs/design.md` has the argument.

## Emission order is per bicommand

`BodyState.emit` appends one bicommand's left statements and then its right
ones, so `(l₁|r₁); (l₂|r₂)` becomes `l₁; r₁; l₂; r₂`. Do not batch the sides
into `l₁; l₂; r₁; r₂`, however tempting it looks given that priming makes them
disjoint. A side may hold a Core `assume`, and batching moves it across the
other side's statements — a later step of one program can then discharge an
obligation the other raised at an earlier step, and nothing reports it.

## The other invariant: scope chain and binding threading must agree

`@[scope(l)]`/`@[scope(r)]` on the `Var` forms are the only scope annotations on
a bicommand: nothing else extends the scope, and a spec is scoped to the
parameters, so it never sees a bi-local at all. `Translate/Bicommands.lean`
mirrors that by hand — it threads Core's `TransBindings` out of the `Var` forms
and out of nothing else. If the two drift, a de Bruijn index
resolves against the wrong binding list and Core aborts with `translateExpr
out-of-range bound variable` — not a type error, and not at the line you
changed. Change one, change the other.

**Priming is not part of that chain, and must not become part of it.** A
right-hand fragment is renamed against `fragment_names` — every variable *that
fragment* mentions — never against a set accumulated alongside the bindings.
The two look interchangeable while every example passes, and are not:
`docs/design.md` has the argument, and what silently breaks.

## Reading the dependency

Vendored sources are the reference, and they are worth reading directly rather
than guessing at:

| Path under `.lake/packages/` | What's there |
|---|---|
| `Strata/Strata/Languages/Core/DDMTransform/Grammar.lean` | Core's dialect — the categories and ops RelRL builds on |
| `Strata/Strata/Cli/Framework.lean` | flag parsing, exit codes, help printing |
| `StrataDDM/StrataDDM/BuiltinDialects/` | `Init`, `StrataDDL`, `StrataHeader` |
| `StrataDDM/StrataDDM/Elab/Core.lean` | the elaborator: scoping, typechecking, `elabCommand` |
