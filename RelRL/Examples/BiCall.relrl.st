// A synchronized call to a `biproc`: WhyRel's `|_ m() _|` on a bimethod. The
// call site uses the callee's *relational* spec, so a bi-spec is a hypothesis
// and not only an obligation. Why it is one fused Core call: docs/design.md.

program RelRL;

biproc double (n : int, out result : int) | (n : int, out result : int)
  requires { Agree n }
  ensures { Agree result }
=
  << result := int.mul(n, 2); | result := int.mul(n, 2); >> ;

// Neither body is unfolded here: `double`'s `ensures` is the whole hypothesis,
// twice. `t`/`t'` are the bi-locals the first call writes and the second reads.
biproc quadruple (n : int, out result : int) | (n : int, out result : int)
  requires { Agree n }
  ensures { Agree result }
=
  Var t : int | t : int ;
  |- Call double (n, out t) | (n, out t) -| ;
  |- Call double (t, out result) | (t, out result) -| ;

// A callee whose `requires` relates the two sides' arguments rather than
// demanding they agree. `offset` below is what needs that.
biproc sum (a : int, b : int, out result : int) | (a : int, b : int, out result : int)
  requires { int.add(a, b) =:= int.add(a, b) }
  ensures { Agree result }
=
  << result := int.add(a, b); | result := int.add(a, b); >> ;

// The sides need not pass the same arguments, or the same number of them: only
// the callee's `requires` has to hold of the pair — here `n + 1` on the left
// against `m + k` on the right.
biproc offset (n : int, out result : int) | (m : int, k : int, out result : int)
  requires { int.add(n, 1) =:= int.add(m, k) }
  ensures { Agree result }
=
  |- Call sum (n, 1, out result) | (m, k, out result) -| ;
