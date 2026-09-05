// The relational assertion language, ported from RelRL's `rformula`
// (`src/parser/ast.ml` in dnaumann/RelRL), on two programs that sum the same
// three numbers in opposite orders.
//
// The expression layer is Core's, spelled as Core spells it — `int.add(a, b)`,
// not `a + b`. The relational layer above it is RelRL's.

program RelRL;

// Shared by both sides, which is what makes it nameable in a `requires`.
const bound : int;
axiom [bound_pos]: int.gt(bound, 0);

biproc sum
  // A spec names the parameters and the file's top-level declarations, never a
  // bi-local. Both sides read the same `bound` — docs/issues.md says why that
  // is wrong and what it would take to give each its own.
  requires { Both (int.gt(bound, 0)) }
=
  // `Var` is the only form that declares; `|- … -| ;` runs one statement on
  // both sides, so it does the initializing.
  Var a : int | a : int ;
  |- a := 1; -| ;
  Var b : int | b : int ;
  |- b := 2; -| ;
  Var c : int | c : int ;
  |- c := 3; -| ;
  Var s : int | s : int ;
  |- s := 0; -| ;
  Var last : int | last : int ;
  |- last := 0; -| ;

  // A relational assert sees both sides as they stand at this point.
  Assert { Agree a /\ Agree s } ;

  <<
    s := int.add(s, a);
    s := int.add(s, b);
    s := int.add(s, c);
    last := c;
  |
    s := int.add(s, c);
    s := int.add(s, b);
    s := int.add(s, a);
    last := a;
  >> ;

  // Every form, on bi-locals — which is why this is an `Assert` in the body and
  // not an `ensures`.
  Assert {
    // `Agree x` — the two sides' `x` hold the same value.
    Agree s
    // `Both (e)` — `e` of the left state, and of the right.
    /\ Both (int.gt(s, 0))
    // One state only: `<| e <]` the left, `[> e |>` the right.
    /\ <| last == 3 <]
    /\ [> last == 1 |>
    // `l =:= r` relates a left expression to a right one.
    /\ last =:= int.add(int.mul(last, 2), 1)
    /\ Agree a /\ Agree b /\ Agree c
    // `~`, `\/`, `=>` and `<=>`; `{ … }` groups, since `( … )` groups a Core
    // expression.
    /\ { ~ Agree last => { Agree s \/ [> s == 0 |> } }
    /\ { Agree s <=> Both (s == 6) }
  } ;

  // `Let` names a value from either program — `[< e <]` reads the left state,
  // `[> e >]` the right — and the body is an ordinary formula over those names.
  // It is the one form that reaches across the two programs at an arbitrary
  // type, and the only one that says more than `=:=`. The names are bound
  // variables, which is why nothing primes them.
  Assert { Let x = [< s <], y = [> s >] :: <| x == y <] } ;
  // An inequality between the two, which `=:=` cannot state.
  Assert { Let x = [< int.add(s, 1) <], y = [> s >] :: <| int.gt(x, y) <] } ;
  // Any Core type, not only the comparable ones.
  Assert { Let p = [< s == 6 <], q = [> s == 6 >] :: <| p && q <] } ;
  // `last` is 3 on the left and 1 on the right, so arithmetic over the two
  // bindings reaches a value neither program holds.
  Assert { Let a = [< last <], b = [> last >] :: <| int.add(a, b) == 4 <] } ;
  // A binding may read what an earlier one declared, from the other side:
  // `b` is the right program's `last` plus the left program's.
  Assert { Let a = [< last <], b = [> int.add(last, a) >] :: <| b == 4 <] } ;

  // A quantifier binds one list per side, either side omittable, or one list
  // both readings share. Nothing bound here is program state, so nothing about
  // it is primed — which is why `Forall i : int | i : int` is refused.
  Assert { Forall k : int :: { Both (int.gt(k, 0)) } => Both (int.le(k, k)) } ;
  Assert { Forall k : int | j : int :: { k =:= j } => { j =:= k } } ;
  Assert { Exists k : int :: Both (k == s) } ;
  // One side alone: the binder exists in that program's reading only.
  Assert { Forall k : int | :: <| int.le(k, int.add(k, s)) <] } ;
  Assert { Forall | j : int :: [> int.le(j, int.add(j, s)) |> } ;
