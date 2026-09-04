// WhyRel's `examples/all_all/factorial`: two loops computing the same
// factorial, one counting up from 0 and the other from 1, aligned so the right
// side runs one step ahead. The offset is what `int.add(i, 1) =:= i` records.

program RelRL;

biproc fact (n : int, out result : int) | (n : int, out result : int)
  requires { Both (int.ge(n, 0)) }
  requires { Agree n }
  ensures { Both (int.gt(result, 0)) }
  ensures { Agree result }
=
  Var i : int | i : int ;
  << i := 0; | i := 1; >> ;
  |- result := 1; -| ;
  While int.lt(i, n) | int.le(i, n) . <| false <] | [> false |> do
    invariant { int.add(i, 1) =:= i }
    invariant { Agree result }
    invariant { <| int.le(0, i) && int.le(i, n) <] }
    invariant { [> int.le(1, i) && int.le(i, int.add(n, 1)) |> }
    invariant { Both (int.gt(result, 0)) }
    <<
      i := int.add(i, 1);
      result := int.mul(result, i);
    |
      result := int.mul(result, i);
      i := int.add(i, 1);
    >> ;
  done ;
