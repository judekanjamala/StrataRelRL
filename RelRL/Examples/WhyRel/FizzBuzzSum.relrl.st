// The second half of WhyRel's `examples/all_all/Veracity/Fizzbuzz`: summing the
// marks over `[0, n/2)` then `[n/2, n)` agrees with summing them the other way
// round. The two sides' loops have different trip counts, so the alignment
// guards let either step alone.

program RelRL;

// WhyRel imports `Fizzbuzz_Theory`, where `count` is a recursive function and
// `count_mid` a lemma Why3 proves by induction. Core sends `count` to SMT
// uninterpreted, so its two defining equations and the splitting lemma are
// axioms here — the same assumption, stated rather than discharged.
function count (m : Map int int, lo : int, hi : int) : int;

axiom [count_empty]:
  forall m : Map int int, lo : int, hi : int ::
    int.ge(lo, hi) ==> count(m, lo, hi) == 0;

axiom [count_step]:
  forall m : Map int int, lo : int, hi : int ::
    int.lt(lo, hi) ==>
      count(m, lo, hi) ==
        int.add(count(m, lo, int.sub(hi, 1)),
                if m[int.sub(hi, 1)] == 1 then 1 else 0);

axiom [count_mid]:
  forall m : Map int int, lo : int, mid : int, hi : int ::
    int.le(lo, mid) && int.le(mid, hi) ==>
      count(m, lo, hi) == int.add(count(m, lo, mid), count(m, mid, hi));

// WhyRel's precondition is a relational `forall` over `getfnval(i, hmap)` on
// `[0, n)`; `Agree hmap` says it for every key, and is what `count` needs to
// take the same value on both sides.
biproc sum (hmap : Map int int, n : int, out result : int)
          | (hmap : Map int int, n : int, out result : int)
  requires { Agree hmap /\ Agree n }
  requires { Both (int.gt(n, 0)) }
  ensures { Agree result }
=
  Var i : int | i : int ;
  Var v : int | v : int ;
  |- result := 0; -| ;

  // Phase 1: the left sums the lower half, the right the upper one. Every
  // invariant is one-sided, which is what makes them survive a step by either.
  << i := 0; | i := int.div(n, 2); >> ;
  While int.lt(i, int.div(n, 2)) | int.lt(i, n) . <| true <] | [> true |> do
    invariant { <| int.le(0, i) && int.le(i, int.div(n, 2)) <] }
    invariant { [> int.le(int.div(n, 2), i) && int.le(i, n) |> }
    invariant { <| result == count(hmap, 0, i) <] }
    invariant { [> result == count(hmap, int.div(n, 2), i) |> }
    |- v := hmap[i]; -| ;
    <<
      if (v == 1) { result := int.add(result, 1); }
    |
      if (v == 1) { result := int.add(result, 1); }
    >> ;
    |- i := int.add(i, 1); -| ;
  done ;

  // Phase 2, with the halves exchanged.
  << i := int.div(n, 2); | i := 0; >> ;
  While int.lt(i, n) | int.lt(i, int.div(n, 2)) . <| true <] | [> true |> do
    invariant { <| int.le(int.div(n, 2), i) && int.le(i, n) <] }
    invariant { [> int.le(0, i) && int.le(i, int.div(n, 2)) |> }
    invariant { <| result ==
                   int.add(count(hmap, 0, int.div(n, 2)),
                           count(hmap, int.div(n, 2), i)) <] }
    invariant { [> result ==
                   int.add(count(hmap, int.div(n, 2), n),
                           count(hmap, 0, i)) |> }
    |- v := hmap[i]; -| ;
    <<
      if (v == 1) { result := int.add(result, 1); }
    |
      if (v == 1) { result := int.add(result, 1); }
    >> ;
    |- i := int.add(i, 1); -| ;
  done ;

  // `count_mid` is what turns each side's two partial sums into the whole.
  Assert { Both (result == count(hmap, 0, n)) } ;
