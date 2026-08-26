# Current state

**Works today**

- `.relrl.st` concrete syntax, parsed by DDM from the `#dialect RelRL`
  declaration: `biproc <name> = << { …left… } | { …right… } >>;`
- **Variable agreement postconditions.** An optional `ensures` clause relates
  the two sides:

  ```
  biproc swap = << { … } | { … } >> ensures
    [agree_a]: a == a',
    [agree_b]: b == b';
  ```

  The two sides' locals are renamed apart under the prime convention — the left
  side keeps its source names, the right side's become `<v>'` — and the sides
  are flattened into one scope — ordinary self-composition — so the agreement is
  an ordinary Core `assert` after both sides have run.
- `StrataDDM.Program` → `Core.Program` translation, with source positions preserved
- SMT-backed verification via Core's unmodified pipeline
- A standalone `relrl` CLI (`verify`, `toCore`) with no `Strata-CLI` dependency

**Not yet**

- **Relational specifications beyond variable agreement.** An `ensures` spec
  relates two *identifiers*; `a == a' + 1` does not parse. This is
  forced by DDM's phase structure, not chosen — see `docs/issues.md`. There are
  also no relational *pre*conditions and no `bimodule`-style specs.
- **Yet to add Biif and Biwhile and Bisync** `biembed` is the only one.
- **Yet to add Objects, classes, methods, modules.** Each side is plain Core commands.
  There is no heap model — deliberately, since the forall-forall examples
  being targeted first don't need one.
