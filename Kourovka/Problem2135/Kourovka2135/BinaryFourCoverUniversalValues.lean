import Kourovka2135.BinaryFourDoubleCoverReflector
import Kourovka2135.BinaryFourMovingKernelLifting
import Kourovka2135.SLTwoFiveReflector
import Kourovka2135.UniversalWordReflector
import Kourovka2135.BinarySplitGoodSetGeneration

/-! Universal order-three values above both concrete central-cover models.
All persistent fibers and the double-cover reflector are proved inputs;
the selected element has order exactly three in the actual ambient group. -/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.BinaryFourCoverUniversalValues

section OrderLift

variable {G Q : Type*} [Group G] [Group Q] [Finite G]

/-- Exact order, rather than merely coprime order, lifts through a p-kernel. -/
theorem exists_order_preserving_lift
    {p : ℕ} (hp : p.Prime) (f : G →* Q) (hf : Function.Surjective f)
    (hker : IsPGroup p f.ker) (y : Q) (hy : ¬ p ∣ orderOf y) :
    ∃ x : G, f x = y ∧ orderOf x = orderOf y := by
  let e := QuotientGroup.quotientKerEquivOfSurjective f hf
  have hy' : ¬ p ∣ orderOf (e.symm y) := by
    rwa [e.symm.orderOf_eq]
  obtain ⟨x, hx, ho⟩ := exists_order_preserving_lift_of_pgroup hp f.ker hker (e.symm y) hy'
  refine ⟨x, ?_, ?_⟩
  · change e (QuotientGroup.mk' f.ker x) = y
    rw [hx, e.apply_symm_apply]
  · simpa only [e.symm.orderOf_eq] using ho

end OrderLift

variable {F : Type} [Field F] [Fintype F] [CharP F 2]
variable [IsSimpleGroup (SLTwo.SL2 F)]
variable (hcard : Fintype.card F = 4)
variable {G : Type} [Group G] [Finite G] [Group.IsPerfect G]
variable (pi : G →* SLTwo.SL2 F) (hpi : Function.Surjective pi)
variable (hR : IsPGroup 2 pi.ker) (hF : pi.ker ≤ frattini G)

include hcard hpi hR hF

/-- The split central-quotient case yields an order-three universal single value. -/
theorem of_split_cover
    (hsolv : ∀ H : Subgroup (SLTwo.SL2 F), H < ⊤ → Group.IsSolvable H)
    (f : G →* SLTwo.SL2 F) (hf : Function.Surjective f) (hker : f.ker ≤ pi.ker)
    (hm : ⁅f.ker, (⊤ : Subgroup G)⁆ = f.ker) :
    ∃ x : G, orderOf x = 3 ∧ ∀ w : OuterWord, x ∈ w.values G := by
  have hdiv : 3 ∣ Nat.card F - 1 := by
    rw [Nat.card_eq_fintype_card, hcard]
  have hB := BinarySplitGoodSetGeneration.isGeneratingGoodSet F hsolv
    (by decide : Odd 3) hdiv
  have hY := BinaryFourMovingKernelLifting.preimage hcard pi hpi hR hF f hf hker hm hB
  obtain ⟨y, hy⟩ := BinarySplitGoodSetGeneration.splitOrderSet_nonempty F hdiv
  have hyorder : orderOf y = 3 := BinarySplitTorusGoodPair.orderOf_mem_splitOrderSet hy
  obtain ⟨x, hx, ho⟩ := exists_order_preserving_lift Nat.prime_two f hf (hR.to_le hker) y
    (by rw [hyorder]; decide)
  refine ⟨x, ho.trans hyorder, fun w => hY.subset_values w ?_⟩
  change f x ∈ BinarySplitTorusGoodPair.splitOrderSet 3
  rw [hx]
  exact hy

/-- The actual matrix double cover also yields an order-three universal single value. -/
theorem of_double_cover
    (f : G →* SLTwoFiveAlternating.S) (hf : Function.Surjective f)
    (hcompat : SLTwoFiveAlternating.toAlternating.comp f =
      (BinaryFourAlternatingEquiv.equiv hcard).toMonoidHom.comp pi)
    (hm : ⁅f.ker, (⊤ : Subgroup G)⁆ = f.ker) :
    ∃ x : G, orderOf x = 3 ∧ ∀ w : OuterWord, x ∈ w.values G := by
  have hpk : (SLTwoFiveAlternating.toAlternating.comp f).ker = pi.ker := by
    rw [hcompat]
    exact MonoidHom.ker_mulEquiv_comp pi (BinaryFourAlternatingEquiv.equiv hcard)
  have hker : f.ker ≤ pi.ker := by
    rw [← hpk]
    intro x hx
    change SLTwoFiveAlternating.toAlternating (f x) = 1
    rw [show f x = 1 from hx, map_one]
  have hY := BinaryFourMovingKernelLifting.preimage hcard pi hpi hR hF f hf hker hm
    SLTwoFiveGoodSet.isGeneratingGoodSet
  have hRp : IsPGroup 2 (SLTwoFiveAlternating.toAlternating.comp f).ker := hpk.symm ▸ hR
  have hFp : (SLTwoFiveAlternating.toAlternating.comp f).ker ≤ frattini G := hpk.symm ▸ hF
  obtain ⟨u, hfu, hu⟩ := exists_order_preserving_lift Nat.prime_two f hf (hR.to_le hker)
    SLTwoFiveReflectorData.uE (by rw [SLTwoFiveReflectorData.orderOf_uE]; decide)
  have horder : orderOf u = 3 := hu.trans SLTwoFiveReflectorData.orderOf_uE
  obtain ⟨b, c, hb, hc, hinv⟩ := BinaryFourDoubleCoverReflector.exists_inputs_inverting
    hcard f hf hRp hFp hm u horder hfu
  refine ⟨u, horder, ?_⟩
  apply UniversalWordReflector.universal_of_good_set_commutator_order_three
    (f ⁻¹' SLTwoFiveGoodSet.Y) hY b ?_ c ?_ u horder hinv
  · change f b ∈ SLTwoFiveGoodSet.Y
    rw [hb]
    exact SLTwoFiveReflector.b_mem_goodSet
  · change f c ∈ SLTwoFiveGoodSet.Y
    rw [hc]
    exact SLTwoFiveReflector.c_mem_goodSet

end Kourovka2135.BinaryFourCoverUniversalValues
