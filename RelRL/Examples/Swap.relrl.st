// Ported from RelRL's `examples/all_all/swap/prog.rl`.

program RelRL;

birelate swap = ( {
    var a : int := 0;
    var b : int := 0;
    a := 3;
    b := 4;
  } | {
    var a : int := 0;
    var b : int := 0;
    b := 3;
    a := 3;
  }
) ensures
  [agree_a]: left_a == right_a,
  [agree_b]: left_b == right_b;
