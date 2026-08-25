/-
  Copyright StrataRelRL Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module

meta import all RelRL.Verify
import StrataDDM.Integration.Lean.HashCommands

meta section

namespace Strata.RelRL.Test

/-! # Grammar tests for the `RelRL` dialect

Each `#strata … #end` block parses at Lean elaboration time, so a grammar
regression is a Lean error on the offending line — visible in the editor, and
fatal to `lake build`. -/

/-! ## Accepted forms -/

def SwapPgm :=
#strata
program RelRL;

birelate swap = ( {
    var a : int := 0;
    a := 3;
    assert [l]: a == 3;
  } | {
    var a : int := 0;
    a := 3;
    assert [r]: a == 3;
  }
);
#end

-- Round-trip through the DDM-generated formatter: pins that `birelate` and
-- `biembed` build the AST shape the grammar claims, not just that the text
-- parsed at all.
/--
info: program RelRL;
birelate swap = ({
  var a : int := 0;
  a := 3;
  assert [l]: a == 3;
} | {
  var a : int := 0;
  a := 3;
  assert [r]: a == 3;
});
-/
#guard_msgs in
#eval IO.println SwapPgm

-- The `ensures` clause is optional, and its operands are `Ident`, not `bool`
-- (see `docs/issues.md`). Both facts are pinned here.
def AgreePgm :=
#strata
program RelRL;

birelate agree = ( {
    var a : int := 0;
    a := 3;
  } | {
    var a : int := 0;
    a := 3;
  }
) ensures [agree_a]: left_a == right_a;
#end

/--
info: program RelRL;
birelate agree = ({
  var a : int := 0;
  a := 3;
} | {
  var a : int := 0;
  a := 3;
}) ensures [agree_a]: left_a == right_a;
-/
#guard_msgs in
#eval IO.println AgreePgm

/-! ## Rejected forms

These pin the two exclusions `docs/design.md` argues for: a `Bicommand` cannot
nest inside a `Bicommand`, and a `birelate` cannot appear inside a side. Both
are properties of the *grammar* (no `Command`-typed argument anywhere in
`Bicommand`), so a parse error is exactly the right assertion. -/

/-- error: unexpected token '('; expected Core.Block -/
#guard_msgs in
def NestedBicommand :=
#strata
program RelRL;
birelate bad = ( ( { var a : int := 0; } | { var b : int := 0; } ) | { var c : int := 0; } );
#end

/-- error: unexpected token 'birelate'; expected '}' -/
#guard_msgs in
def BirelateInsideSide :=
#strata
program RelRL;
birelate outer = ( { birelate inner = ( { } | { } ); } | { } );
#end

/-! ## Lowering

The grammar is only half the contract; the other half is that `Translate` can
walk what it produces. -/

def swapCtx : Lean.Parser.InputContext :=
  Lean.Parser.mkInputContext SwapPgm.source SwapPgm.fileName

/-- info: decls=1 diags=0 -/
#guard_msgs in
#eval do
  let (core, diags) := RelRL.TranslateM.run (RelRL.translateProgram SwapPgm.program swapCtx)
  IO.println s!"decls={(Core.Program.decls core).length} diags={diags.size}"

def agreeCtx : Lean.Parser.InputContext :=
  Lean.Parser.mkInputContext AgreePgm.source AgreePgm.fileName

-- Pins the renaming: each side's `a` becomes `left_a` / `right_a`, the sides
-- are flattened into one scope, and the agreement assert lands after both.
/--
info: program Core;
procedure agree ()
{
  biembed: {
    var left_a : int := 0;
    left_a := 3;
    var right_a : int := 0;
    right_a := 3;
    assert [agree_a]: left_a == right_a;
  }
};
-/
#guard_msgs in
#eval do
  let (core, _) := RelRL.TranslateM.run (RelRL.translateProgram AgreePgm.program agreeCtx)
  IO.println (StrataDDM.Program.toString (Strata.coreToStrataProgram core))

end Test
end RelRL
end Strata
