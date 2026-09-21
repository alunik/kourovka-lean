import Kourovka2135.PSL33GoodSets
import Kourovka2135.GeneratingGoodSetPerfect

/-! Perfectness of the actual PSL3(F3), derived from the already checked
generating commutator class. No simplicity or classification is assumed. -/

set_option autoImplicit false

namespace Kourovka2135.PSLThreeThreePerfect
open PSL33GoodSets

instance : Group.IsPerfect Q := good13.isPerfect ⟨y13, y13_mem⟩

end Kourovka2135.PSLThreeThreePerfect
