// What a bicommand sequence buys: an `Assert` between two aligned steps sees
// each side exactly as it stands there. Without one the alignment is
// unobservable — docs/design.md.

program RelRL;

biproc aligned
  ensures { Agree a /\ Agree b }
=
  |- var a : int := 0; -| ;
  |- var b : int := 0; -| ;
  <<
    a := 1;
  |
    a := 1;
  >> ;
  // Both sides have taken their first step and no more: `a` is set, `b` is not.
  Assert { Agree a /\ Both (b == 0) } ;
  <<
    b := 2;
  |
    b := 2;
  >> ;
