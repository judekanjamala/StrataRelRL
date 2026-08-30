// Ported from RelRL's `examples/all_all/swap/prog.rl`, whose bimodule aligns
// two commuting steps as `( f | g ); ( g | f );` — a sequence of bicommands,
// one per aligned step. See docs/design.md for the delimiters and the
// alignment.

program RelRL;

biproc swap
  ensures { Agree a /\ Agree b }
=
  |- var a : int := 0; -| ;
  |- var b : int := 0; -| ;
  // The left assigns `a` first, the right `b` first.
  <<
    a := 3;
  |
    b := 3;
  >> ;
  <<
    b := 3;
  |
    a := 3;
  >> ;
