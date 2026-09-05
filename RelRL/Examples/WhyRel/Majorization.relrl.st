// WhyRel's `examples/all_all/majorization` (Naumann, "Thirty-seven years of
// relational Hoare logic"): two loops that decrement the same counter on
// different schedules, the left's product staying strictly above the right's.
// The alignment guards are what let each side run its own off-beat iterations.

program RelRL;

biproc m (x : int, out result : int) | (x : int, out result : int)
  requires { Agree x }
  requires { Both (int.ge(x, 4)) }
  ensures { Let a = [< result <], b = [> result >] :: <| int.gt(a, b) <] }
=
  Var y : int | y : int ;
  Var z : int | z : int ;
  Var w : int | w : int ;
  |- y := x; -| ;
  << z := 24; | z := 16; >> ;
  |- w := 0; -| ;
  While int.gt(y, 4) | int.gt(y, 4) .
    <| int.mod(w, 2) != 0 <] | [> int.mod(w, 3) != 0 |> do
    invariant { Agree y }
    invariant { Both (int.ge(y, 4)) }
    invariant { [> int.gt(z, 0) |>
                /\ { Let a = [< z <], b = [> z >] :: <| int.gt(a, b) <] } }
    // Reached only when neither side may step alone, so both guards hold and
    // `If`'s agreement obligation is discharged by the alignment guards.
    If int.mod(w, 2) == 0 | int.mod(w, 3) == 0 then
      << z := int.mul(z, y); | z := int.mul(z, 2); >> ;
      |- y := int.sub(y, 1); -| ;
    end ;
    |- w := int.add(w, 1); -| ;
  done ;
  |- result := z; -| ;
