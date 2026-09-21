import Kourovka2135.CanonicalOddGoodSet
import Kourovka2135.GoodSetObstruction

/-! The odd-prime branch reduces to a good set in the canonical central cover. -/

set_option autoImplicit false
universe u
namespace Kourovka2135
variable {G : Type u} [Group G] [Finite G] {w : OuterWord} {p : ℕ}

theorem OrderMinimalException.no_canonical_good_set_with_coprime_element
    (h : OrderMinimalException w p G) (hp : p.Prime) (hodd : p ≠ 2)
    (hnoncentral : ¬ solubleRadical G ≤ Subgroup.center G)
    {Y : Set (G ⧸ ⁅solubleRadical G, (⊤ : Subgroup G)⁆)}
    (hY : IsGeneratingGoodSet Y)
    {y : G ⧸ ⁅solubleRadical G, (⊤ : Subgroup G)⁆}
    (hy : y ∈ Y) (hne : y ≠ 1) (hyp : ¬ p ∣ orderOf y) : False := by
  let : Fact p.Prime := ⟨hp⟩
  let : Group.IsPerfect G := h.isPerfect hp
  have hR : IsPGroup p (solubleRadical G) := by
    rw [h.radical_eq_pCore hp]
    exact pCore_isPGroup
  have hF : solubleRadical G ≤ frattini G := (h.radical_eq_frattini hp).le
  have hpre := hY.preimage_quotient_commutator_of_odd_frattini hp hodd
    (solubleRadical G) hR hF
  exact h.no_good_preimage_with_coprime_element hp hnoncentral
    (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _) hpre hy hne hyp

end Kourovka2135
