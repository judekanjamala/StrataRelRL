// WhyRel's `examples/all_all/monofact`: one factorial program against itself,
// on a larger and a smaller `n`. What it needs that `=:=` cannot say is the
// cross-side *inequality* — `Rel int.ge (result | result)`, WhyRel's
// `[< result <] >= [> result >]`.

program RelRL;

biproc fact (n : int, out result : int) | (n : int, out result : int)
  requires { Both (int.ge(n, 0)) }
  requires { Rel int.ge (n | n) }
  ensures { Rel int.ge (result | result) }
=
  Var i : int | i : int ;
  Var r : int | r : int ;
  |- i := 0; -| ;
  |- r := 1; -| ;
  // The left runs the extra iterations alone, which is what its alignment
  // guard permits once the right has finished.
  While int.lt(i, n) | int.lt(i, n) . [> i == n |> | [> false |> do
    invariant { Both (int.le(0, i) && int.le(i, n)) }
    invariant { Rel int.ge (i | i) }
    invariant { [> int.lt(i, n) |> => Agree i }
    invariant { Rel int.ge (r | r) /\ Both (int.ge(r, 1)) }
    |- i := int.add(i, 1); -| ;
    |- r := int.mul(r, i); -| ;
  done ;
  |- result := r; -| ;
