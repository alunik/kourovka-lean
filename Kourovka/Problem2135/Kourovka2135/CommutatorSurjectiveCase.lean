import Kourovka2135.CentralWordValues
import Kourovka2135.LeafCase
import Kourovka2135.NormalComplementOperations

/-! The exact forward theorem for groups with a surjective commutator map.
The surjectivity premise is explicit; Ore's theorem is not proved here. -/

set_option autoImplicit false
universe u
namespace Kourovka2135
variable {G : Type u} [Group G] [Finite G]

theorem problem2135_of_commutatorSurjective (hG : CommutatorSurjective G) :
    Problem2135 G := by
  intro w p hp h
  have hleaf : ProductOrderCondition .leaf p G := by
    intro x _ y _ hxp hyp
    have hw : w.values G = Set.univ := w.values_eq_univ_of_commutatorSurjective hG
    exact h x (hw ▸ Set.mem_univ _) y (hw ▸ Set.mem_univ _) hxp hyp
  exact HasNormalPComplement.subgroup hp (hasNormalPComplement_of_leaf_condition hp hleaf)
    (w.verbalSubgroup G)

end Kourovka2135
