// `Var` is the only form that declares: one variable per side under its own
// name, either side omittable, nothing initialized. Why nothing else extends
// the scope: docs/design.md.

program RelRL;

// Both programs leave their result at 6. The left gets there through an
// accumulator; the right has no such variable at all.
biproc differing
=
  // The right side is primed like any other, so `s =:= t` is `s == t'`.
  Var s : int | t : int ;
  // Left only. `Var | u : int ;` declares one on the right alone.
  Var acc : int | ;
  <<
    acc := 6;
    s := acc;
  |
    t := 6;
  >> ;
  Assert { s =:= t } ;

// `Var` does not need the names to differ — the right side is primed, so this
// is WhyRel's own `Var i:int | i:int` and the two `n`s stay apart.
biproc repeated
=
  Var n : int | n : int ;
  <<
    n := 1;
  |
    n := 2;
  >> ;
  Assert { <| n == 1 <] /\ [> n == 2 |> } ;

// The same name on both sides is the pair `n`/`n'` — one variable each program
// has, which is what `Agree n` needs.
biproc shared
=
  Var n : int | n : int ;
  <<
    n := 1;
  |
    n := 1;
  >> ;
  Assert { Agree n } ;
