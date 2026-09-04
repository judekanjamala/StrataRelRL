// WhyRel's `examples/all_all/equiv-check` (Churchill et al., PLDI'19): a
// doubly-nested multiplication against a single accumulating loop. The
// alignment pairs one outer iteration with one, so the inner loop sits inside a
// split's left side as a plain Core `while`.

program RelRL;

biproc multiply (n : int, m : int, out result : int)
              | (n : int, m : int, out result : int)
  requires { Both (int.ge(n, 0)) /\ Both (int.ge(m, 0)) }
  requires { Agree n /\ Agree m }
  ensures { Agree result }
=
  Var i : int | i : int ;
  Var j : int | ;
  // WhyRel's `ghost tmp`, holding `result` from before the inner loop. Its
  // comment there explains why: Why3's `old` in an invariant means procedure
  // entry, so the loop cannot name the value it started from.
  Var tmp : int | ;
  // WhyRel gives `result` its type's default; Core leaves an `out` parameter
  // arbitrary, so the zero is explicit here.
  |- result := 0; -| ;
  |- i := 0; -| ;
  While int.lt(i, n) | int.lt(i, n) . <| false <] | [> false |> do
    invariant { Both (int.le(0, i) && int.le(i, n)) }
    invariant { Agree i }
    invariant { Agree result }
    << j := 0; | >> ;
    <<
      tmp := result;
      while (int.lt(j, m))
      invariant int.le(0, j) && int.le(j, m)
      invariant result == int.add(tmp, j)
      {
        result := int.add(result, 1);
        j := int.add(j, 1);
      }
    |
      result := int.add(result, m);
    >> ;
    Assert { Agree result } ;
    |- i := int.add(i, 1); -| ;
  done ;
