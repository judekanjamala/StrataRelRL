/-
  Copyright StrataRelRL Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module

public import Strata.Languages.Core.DDMTransform.Grammar
public import StrataDDM.HNF
public import StrataDDM.Integration.Lean.OfAstM
import StrataDDM.Integration.Lean -- shake: keep

public section

namespace Strata

#dialect
dialect RelRL;
import Core;

category Bicommand;


category RelSpec;
op rel_agree (label : Ident, lhs : Ident, rhs : Ident) : RelSpec =>
  "[" label "]: " lhs " == " rhs;

category RelEnsures;
op rel_ensures (specs : CommaSepBy RelSpec) : RelEnsures => " ensures " specs;

// Bicommand is deliberately NOT a `Command`. Refer docs/design.md
op biproc (name : Ident, body : Bicommand, rel : Option RelEnsures) : Command =>
  "biproc " name " = " body rel ";";

op biembed (left : Block, right : Block) : Bicommand => "<<" left " | " right ">>";


#end

end Strata
end
