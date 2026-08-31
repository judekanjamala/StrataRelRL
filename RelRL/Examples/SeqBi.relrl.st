// What a bicommand sequence buys: an `Assert` between two aligned steps sees
// each side exactly as it stands there, because lowering interleaves per
// bicommand rather than batching each side — docs/design.md.

program RelRL;

biproc aligned
=
  Var a : int | a : int ;
  |- a := 0; -| ;
  Var b : int | b : int ;
  |- b := 0; -| ;
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
  // A spec names only what the caller can see, so a claim about bi-locals is an
  // `Assert` here rather than an `ensures` — docs/design.md.
  Assert { Agree a /\ Agree b } ;
