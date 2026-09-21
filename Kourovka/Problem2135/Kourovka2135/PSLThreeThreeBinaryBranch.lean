import Kourovka2135.PSLThreeThreeSimpleModelBounds
import Kourovka2135.PSLThreeThreeMinimalException

/-! Removal of the actual binary PSL3(F3) least-exception branch, after
discharging its module input with the seven concrete simple models. -/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135

theorem OrderMinimalException.false_of_binary_pslThreeThree_quotient_complete
    {G : Type} [Group G] [Finite G] {w : OuterWord}
    (h : OrderMinimalException w 2 G)
    (e : (G ⧸ solubleRadical G) ≃* PSL33GoodSets.Q) : False :=
  h.false_of_binary_pslThreeThree_quotient
    PSLThreeThreeSimpleModelBounds.binary_module_bound e

end Kourovka2135
