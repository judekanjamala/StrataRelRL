// Ported from RelRL's `examples/all_all/swap/prog.rl`.

program RelRL;

biproc swap = << {
    var a : int := 0;
    var b : int := 0;
    a := 3;
    b := 3;
  } | {
    var a : int := 0;
    var b : int := 0;
    b := 3;
    a := 3;
  }
>> ensures
  [agree_a]: a == a',
  [agree_b]: b == b';
