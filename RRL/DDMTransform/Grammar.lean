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
dialect RRL;
import Core;

category Bicommand;
op biembed (left : Command, right : Command) : Bicommand => "(" left " | " right ")";
op command_bicommand (b : Bicommand) : Command => b;

#end

end Strata
end
