// The two declaration forms: `Var` when the sides' names differ (either side
// omittable, nothing initialized), `|- … -| ;` when they share one. Why the
// split is forced rather than chosen: docs/design.md.

program RelRL;

// Both programs leave their result at 6. The left gets there through an
// accumulator; the right has no such variable at all.
biproc differing
  ensures { s =:= t }
=
  // Neither is primed, so `s =:= t` relates them directly.
  Var s : int | t : int ;
  // Left only. `Var | u : int ;` declares one on the right alone.
  Var acc : int | ;
  <<
    acc := 6;
    s := acc;
  |
    t := 6;
  >> ;

// A shared name goes through the synchronized form, which declares the pair
// `n`/`n'` from one source name.
biproc shared
  ensures { Agree n }
=
  |- var n : int; -| ;
  <<
    n := 1;
  |
    n := 1;
  >> ;
