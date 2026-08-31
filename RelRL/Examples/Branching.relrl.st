// The conditional bicommands: `If` (with and without `else`), whose guards must
// be proved to agree, and `If4`, whose need not. Why one carries an obligation
// and the other a branch per combination: docs/design.md.

program RelRL;

// `If` puts both sides under one Core `if`. That is faithful only because the
// guards are proved equal first — the `if_guards_1` obligation below.
biproc agreeing
=
  |- var n : int; -| ;
  |- var r : int := 0; -| ;
  Assume { Agree n } ;
  If int.gt(n, 0) | int.gt(n, 0) then
    << r := 1; | r := 1; >> ;
  else
    << r := 2; | r := 2; >> ;
  end ;
  Assert { Agree r } ;

// The else-less form, as WhyRel writes it.
biproc no_else
=
  |- var n : int; -| ;
  |- var r : int := 0; -| ;
  Assume { Agree n } ;
  If int.gt(n, 0) | int.gt(n, 0) then
    << r := 1; | r := 1; >> ;
  end ;
  Assert { Agree r } ;

// `If4` is for guards that need not agree: no obligation, one branch per
// combination. Here the two programs hold *different* flags.
biproc four_way
=
  Var a : bool | b : bool ;
  Var r : int  | q : int ;
  If4 a | b
  thenThen
    << r := 1; | q := 1; >> ;
  thenElse
    << r := 2; | q := 2; >> ;
  elseThen
    << r := 3; | q := 3; >> ;
  elseElse
    << r := 4; | q := 4; >> ;
  end ;
  Assert { r =:= q } ;
