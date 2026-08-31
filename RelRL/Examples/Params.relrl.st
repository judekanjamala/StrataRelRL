// Biproc parameters and returns. Each side's are a Core `Bindings`, so `out`
// and `inout` come from Core; the right side is primed like every other
// right-side name. Why the parens are per side: docs/status.md.

program RelRL;

// WhyRel's `meth double (n:int|n:int) : (int|int)`. Naming the output `result`
// gives WhyRel's spelling, and `Agree result` then means what it does there.
// `requires` is what makes this provable: without it `n` and `n'` are unrelated.
biproc double (n : int, out result : int) | (n : int, out result : int)
  requires { Agree n }
  ensures { Agree result }
=
  << result := int.mul(n, 2); | result := int.mul(n, 2); >> ;

// The sides need not agree on names, count or shape — only the relation stated
// by `requires` and `ensures` has to hold.
biproc asymmetric (a : int, out r : int) | (b : int, c : int, out q : int)
  requires { a =:= b }
  ensures { r =:= q }
=
  << r := a; | q := int.sub(int.add(b, c), c); >> ;

// An `inout` parameter, from Core's own binding syntax.
biproc bump (inout x : int) | (inout x : int)
  requires { Agree x }
  ensures { Agree x }
=
  << x := int.add(x, 1); | x := int.add(x, 1); >> ;
