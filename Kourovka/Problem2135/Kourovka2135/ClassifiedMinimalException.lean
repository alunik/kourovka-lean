import Kourovka2135.MinimalSimpleModels
import Kourovka2135.MinimalSimpleReduction

/-! The explicit classification assumption applied to the already proved minimal-simple reduction. -/

set_option autoImplicit false
universe u
namespace Kourovka2135
variable {G : Type u} [Group G] [Finite G] {w : OuterWord} {p : ℕ}

theorem OrderMinimalException.radical_quotient_has_classified_model
    (classification : MinimalSimpleClassification.{u})
    (h : OrderMinimalException w p G) (hp : p.Prime)
    (hnoncentral : ¬ solubleRadical G ≤ Subgroup.center G) :
    IsMinimalSimpleModel (G ⧸ solubleRadical G) := by
  let : IsSimpleGroup (G ⧸ solubleRadical G) := h.quotient_radical_isSimple hp
  exact classification (G ⧸ solubleRadical G)
    (h.quotient_radical_not_isMulCommutative hp)
    (h.quotient_radical_proper_subgroup_isSolvable hp hnoncentral)

end Kourovka2135
