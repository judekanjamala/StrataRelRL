// WhyRel's `examples/all_all/Veracity/Simple_IO`: two file-system routines,
// each looping, commute. With no heap and no theory imports the file system is
// a `Map int (Map int int)` passed `inout`, so each side gets its own —
// docs/status.md on globals, CLAUDE.md on the `--use-array-theory` this needs.

program RelRL;

type FS := Map int (Map int int);

// `f1` copies file `a` over file `b`, twenty times; `f2` copies line 0 of `c`
// to line 0 of `d`, ten times. WhyRel's `fname_1 … fname_4` are `a … d`. The
// left program runs `f1; f2`, the right `f2; f1`.
//
// WhyRel's postcondition is a relational `forall` over `content(fs, f, l)`;
// with the file system one value, `Agree fs` says the same thing.
biproc simpleio (inout fs : FS, a : int, b : int, c : int, d : int)
              | (inout fs : FS, a : int, b : int, c : int, d : int)
  requires { Agree fs }
  requires { Agree a /\ Agree b /\ Agree c /\ Agree d }
  requires { Both (b != c && a != d && b != d) }
  requires { Both (c != d) }
  ensures { Agree fs }
=
  Var k : int | k : int ;
  Var z : int | z : int ;
  Var temp : int | temp : int ;
  <<
    k := 0;
    while (int.lt(k, 20))
    invariant int.le(0, k) && int.le(k, 20)
    invariant forall f : int :: f != b ==> fs[f] == (old fs)[f]
    invariant fs[b] == if int.gt(k, 0) then (old fs)[a] else (old fs)[b]
    {
      fs := fs[b := fs[a]];
      k := int.add(k, 1);
    }
    z := 0;
    while (int.lt(z, 10))
    invariant int.le(0, z) && int.le(z, 10)
    invariant forall f : int :: f != b && f != d ==> fs[f] == (old fs)[f]
    invariant fs[b] == (old fs)[a]
    invariant fs[d] ==
      if int.gt(z, 0) then (old fs)[d][0 := (old fs)[c][0]] else (old fs)[d]
    {
      temp := fs[c][0];
      fs := fs[d := fs[d][0 := temp]];
      z := int.add(z, 1);
    }
  |
    z := 0;
    while (int.lt(z, 10))
    invariant int.le(0, z) && int.le(z, 10)
    invariant forall f : int :: f != d ==> fs[f] == (old fs)[f]
    invariant fs[d] ==
      if int.gt(z, 0) then (old fs)[d][0 := (old fs)[c][0]] else (old fs)[d]
    {
      temp := fs[c][0];
      fs := fs[d := fs[d][0 := temp]];
      z := int.add(z, 1);
    }
    k := 0;
    while (int.lt(k, 20))
    invariant int.le(0, k) && int.le(k, 20)
    invariant forall f : int :: f != b && f != d ==> fs[f] == (old fs)[f]
    invariant fs[d] == (old fs)[d][0 := (old fs)[c][0]]
    invariant fs[b] == if int.gt(k, 0) then (old fs)[a] else (old fs)[b]
    {
      fs := fs[b := fs[a]];
      k := int.add(k, 1);
    }
  >> ;
