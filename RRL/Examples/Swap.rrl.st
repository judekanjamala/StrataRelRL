program RRL;
//
// Ported from RelRL's `examples/all_all/swap/prog.rl`.
//
// The original RelRL program relates two implementations of a method `m`
// that writes to two independent fields `a` and `b` of an object, in
// opposite orders:
//
//   module A0: meth m(self, k) = f(self, k); g(self, k);   // a := k; b := k
//   module A1: meth m(self, k) = g(self, k); f(self, k);   // b := k; a := k
//
//   bimodule A_REL (A0 | A1):
//     meth m(...) requires Agree self, Agree k
//                 ensures  Agree {self}`a /\ Agree {self}`b
//       = ( f(self,k) | g(self,k) );
//         ( g(self,k) | f(self,k) );
//
// i.e. writing to `a` then `b` is observationally equivalent to writing to
// `b` then `a`, since the two writes commute (they touch disjoint fields).
//
// Our RRL dialect does not yet support classes, methods, or relational
// pre/postconditions (`Agree`, `bimodule`) -- only a single top-level
// `biembed (left | right)` pairing two ordinary Core command blocks. So
// this is ported down to the essence of the example: plain `a`/`b`
// variables (standing in for the object's fields) written in opposite
// orders on each side, with each side asserting its own (non-relational)
// postcondition that the commuting writes still reach the same final
// state. A real relational postcondition (`a_left == a_right`) would
// require the bicommand-level assertions this dialect doesn't support yet.
//
( {
    var a : int := 0;
    var b : int := 0;
    a := 3;
    b := 3;
    assert [left_a_then_b]: a == 3;
    assert [left_a_then_b]: b == 3;
  }; | {
    var a : int := 0;
    var b : int := 0;
    b := 3;
    a := 3;
    assert [right_b_then_a]: a == 3;
    assert [right_b_then_a]: b == 3;
  };
)
