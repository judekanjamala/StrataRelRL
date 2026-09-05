// WhyRel's `examples/all_all/monofact`: one factorial program against itself,
// on a larger and a smaller `n`. What it needs that `=:=` cannot say is the
// cross-side *inequality*, WhyRel's `[< result <] >= [> result >]` — a `Let`
// naming each side's value, then comparing the two names.

program RelRL;

biproc fact (n : int, out result : int) | (n : int, out result : int)
  requires { Both (int.ge(n, 0)) }
  requires { Let a = [< n <], b = [> n >] :: <| int.ge(a, b) <] }
  ensures { Let a = [< result <], b = [> result >] :: <| int.ge(a, b) <] }
=
  Var i : int | i : int ;
  Var r : int | r : int ;
  |- i := 0; -| ;
  |- r := 1; -| ;
  // The left runs the extra iterations alone, which is what its alignment
  // guard permits once the right has finished.
  While int.lt(i, n) | int.lt(i, n) . [> i == n |> | [> false |> do
    invariant { Both (int.le(0, i) && int.le(i, n)) }
    invariant { Let a = [< i <], b = [> i >] :: <| int.ge(a, b) <] }
    invariant { [> int.lt(i, n) |> => Agree i }
    invariant { { Let a = [< r <], b = [> r >] :: <| int.ge(a, b) <] }
                /\ Both (int.ge(r, 1)) }
    |- i := int.add(i, 1); -| ;
    |- r := int.mul(r, i); -| ;
  done ;
  |- result := r; -| ;
