// WhyRel's `examples/all_all/Veracity/Fizzbuzz`: marking the multiples of 3
// then of 5 agrees with marking 5 then 3. WhyRel's global `hmap` is an `inout`
// parameter here, so each side gets its own — docs/status.md on globals,
// CLAUDE.md on the `--use-array-theory` this file needs.

program RelRL;

// WhyRel states the postcondition as a relational `forall` over
// `getfnval(i, hmap)`; with the map one value, `Agree hmap` says the same.
// Each loop's invariant is then the closed form of the map so far, not
// WhyRel's pointwise facts: those pin down no key outside `[0, n)`, so they
// cannot give `Agree hmap`, which is agreement at every key.
biproc fizzbuzz (inout hmap : Map int int, n : int)
               | (inout hmap : Map int int, n : int)
  requires { Agree n }
  requires { Both (int.gt(n, 0)) }
  requires { Both (forall i : int :: hmap[i] == 0) }
  ensures { Agree hmap }
=
  Var i : int | i : int ;

  // First pass: the left marks the multiples of 3, the right those of 5.
  |- i := 0; -| ;
  While int.lt(i, n) | int.lt(i, n) . <| false <] | [> false |> do
    invariant { Agree i }
    invariant { Both (int.le(0, i) && int.le(i, n)) }
    invariant { <| forall j : int ::
                     hmap[j] == (if int.le(0, j) && int.lt(j, i) && int.mod(j, 3) == 0
                                 then 1 else 0) <] }
    invariant { [> forall j : int ::
                     hmap[j] == (if int.le(0, j) && int.lt(j, i) && int.mod(j, 5) == 0
                                 then 1 else 0) |> }
    <<
      if (int.mod(i, 3) == 0) { hmap := hmap[i := 1]; }
      i := int.add(i, 1);
    |
      if (int.mod(i, 5) == 0) { hmap := hmap[i := 1]; }
      i := int.add(i, 1);
    >> ;
  done ;

  // Second pass, with the two divisors exchanged.
  |- i := 0; -| ;
  While int.lt(i, n) | int.lt(i, n) . <| false <] | [> false |> do
    invariant { Agree i }
    invariant { Both (int.le(0, i) && int.le(i, n)) }
    invariant { <| forall j : int ::
                     hmap[j] == (if (int.le(0, j) && int.lt(j, n) && int.mod(j, 3) == 0)
                                    || (int.le(0, j) && int.lt(j, i) && int.mod(j, 5) == 0)
                                 then 1 else 0) <] }
    invariant { [> forall j : int ::
                     hmap[j] == (if (int.le(0, j) && int.lt(j, n) && int.mod(j, 5) == 0)
                                    || (int.le(0, j) && int.lt(j, i) && int.mod(j, 3) == 0)
                                 then 1 else 0) |> }
    <<
      if (int.mod(i, 5) == 0) { hmap := hmap[i := 1]; }
      i := int.add(i, 1);
    |
      if (int.mod(i, 3) == 0) { hmap := hmap[i := 1]; }
      i := int.add(i, 1);
    >> ;
  done ;
