// Ported from RelRL's `examples/all_all/swap/prog.rl`, whose bimodule relates
// two programs that call the same commuting methods in opposite orders. The
// callees are Core procedures; a call site uses their spec, not their body.

program RelRL;

// WhyRel's `meth f (self:K, k:int)`, which writes `self.a`. With no heap, the
// field it writes is an `out` parameter instead.

procedure f (k : int, out a : int)
  spec {
    ensures a == k;
  }
{
  a := k;
};

procedure g (k : int, out b : int)
  spec {
    ensures b == k;
  }
{
  b := k;
};

// WhyRel's `meth m`: `( f | g ); ( g | f );`. The bicommand *sequence* is the
// alignment — the left's `f` is lined up with the right's `g`, and the two
// calls that follow with each other.
biproc m (k : int, out a : int, out b : int) | (k : int, out a : int, out b : int)
  requires { Agree k }
  ensures { Agree a /\ Agree b }
=
  << call f(k, out a); | call g(k, out b); >> ;
  << call g(k, out b); | call f(k, out a); >> ;

// WhyRel's `meth m2`: `( f; g | g; f )`, the same two programs aligned as one
// step instead of two. Lowering interleaves per bicommand, so this is *not* the
// same Core as `m` — compare the two under `relrl toCore`.
biproc m2 (k : int, out a : int, out b : int) | (k : int, out a : int, out b : int)
  requires { Agree k }
  ensures { Agree a /\ Agree b }
=
  <<
    call f(k, out a);
    call g(k, out b);
  |
    call g(k, out b);
    call f(k, out a);
  >> ;
