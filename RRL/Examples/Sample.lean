import RRL.DDMTransform.Grammar
import StrataDDM.Integration.Lean

namespace Strata
namespace RRLDDM

set_option maxHeartbeats 400000

#strata_gen RRL

/- Sample RRL program fragment. -/
#check Bicommand.biembed

end RRLDDM
end Strata
