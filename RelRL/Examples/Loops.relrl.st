// The loop bicommands, ported from WhyRel's `Biwhile`: lockstep, the general
// form with alignment guards, and the one-sided `WhileL`/`WhileR`. What each
// lowers to and where it comes from: docs/design.md.

program RelRL;

// Lockstep. One Core loop drives both sides; the `lockstep` invariant, that the
// two guards agree, is what makes that faithful.
biproc lockstep
  ensures { Agree s }
=
  |- var n : int; -| ;
  |- var s : int := 0; -| ;
  Assume { Agree n } ;
  While int.gt(n, 0) | int.gt(n, 0) do
    invariant { Agree n }
    invariant { Agree s }
    << s := int.add(s, n); n := int.sub(n, 1);
    |  s := int.add(s, n); n := int.sub(n, 1); >> ;
  done ;

// Alignment guards let one side step alone: `<| true <] | <| true <]` permits
// either, so this runs the left to completion and then the right. The loop
// carries an `align` invariant ruling out a state where neither side may step.
biproc aligned
  ensures { i =:= j }
=
  Var i : int | j : int ;
  << i := 0; | j := 0; >> ;
  While int.lt(i, 4) | int.lt(j, 4) . <| true <] | <| true <] do
    invariant { <| int.le(i, 4) <] }
    invariant { [> int.le(j, 4) |> }
    << i := int.add(i, 1); | j := int.add(j, 1); >> ;
  done ;

// One-sided: a loop only the left program runs. The body still names both
// sides, and it is the body that says the right one stands still.
biproc left_only
  ensures { i =:= j }
=
  Var i : int | j : int ;
  << i := 0; | j := 4; >> ;
  WhileL int.lt(i, 4) do
    invariant { <| int.le(i, 4) <] }
    << i := int.add(i, 1); | >> ;
  done ;

biproc right_only
  ensures { i =:= j }
=
  Var i : int | j : int ;
  << i := 4; | j := 0; >> ;
  WhileR int.lt(j, 4) do
    invariant { [> int.le(j, 4) |> }
    << | j := int.add(j, 1); >> ;
  done ;
