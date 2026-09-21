import Kourovka2135.PSLThreeThreeFrattiniLifting
import Kourovka2135.DerivedCentralization

/-! A concrete triple-commutator obstruction for binary covers of PSL3(F3).
The finite matrix calculation is unconditional. Its application to Frattini
covers explicitly retains the one unresolved binary-module bound.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
noncomputable section

namespace Kourovka2135.PSLThreeThreeOrderObstruction

open PSL33GoodSets
open PSLThreeThreeSemidihedralData (projectiveEquiv)

/-- A root element already present in the checked generating certificate. -/
def conjugator : SL33Witnesses.S := SL33Witnesses.certMatrix9

def triple : SL33Witnesses.S :=
  paperCommutator (paperCommutator conjugator SL33Witnesses.a13) SL33Witnesses.a13

/-- Ordinary finite verification; no external order assertion is used. -/
theorem triple_order : orderOf triple = 8 := by
  apply orderOf_eq_prime_pow (p := 2) (n := 2)
  · decide +kernel
  · decide +kernel

theorem projected_triple_order :
    orderOf (paperCommutator (paperCommutator (q conjugator) y13) y13) = 8 := by
  have h := orderOf_injective projectiveEquiv.toMonoidHom projectiveEquiv.injective triple
  change orderOf (q triple) = orderOf triple at h
  rw [triple_order] at h
  simpa only [triple, paperCommutator, map_mul, map_inv, y13] using h

/-- One full good-class preimage already rules out every outer-word condition.
No kernel hypothesis is needed in this last group-theoretic step. -/
theorem not_condition_of_good_preimage
    {G : Type} [Group G] [Finite G] (pi : G →* Q)
    (hpi : Function.Surjective pi) (hgood : IsGeneratingGoodSet (pi ⁻¹' Y13))
    (w : OuterWord) : ¬ ProductOrderCondition w 2 G := by
  intro h
  obtain ⟨x, hx, hxp⟩ := exists_coprime_order_lift_of_surjective
    Nat.prime_two pi hpi y13 (by rw [order_y13]; decide)
  have hxval : x ∈ (OuterWord.derivedWord w.height).values G := by
    apply hgood.subset_values
    change pi x ∈ Y13
    rw [hx]
    exact y13_mem
  have hd : ProductOrderCondition (OuterWord.derivedWord w.height) 2 G := by
    intro a ha b hb hap hbp
    exact h a (w.derivedWord_values_subset w.height le_rfl ha)
      b (w.derivedWord_values_subset w.height le_rfl hb) hap hbp
  obtain ⟨z, hz⟩ := hpi (q conjugator)
  have hnot := hd.not_dvd_orderOf_tripleCommutator hxval hxp z
  have himage : pi (paperCommutator (paperCommutator z x) x) =
      paperCommutator (paperCommutator (q conjugator) y13) y13 := by
    simp only [paperCommutator, map_mul, map_inv, hz, hx]
  have hdiv := orderOf_map_dvd pi (paperCommutator (paperCommutator z x) x)
  rw [himage, projected_triple_order] at hdiv
  exact hnot ((by decide : 2 ∣ 8).trans hdiv)

/-- Conditional family endpoint; the outstanding module theorem is visible. -/
theorem not_productOrderCondition
    (hmodule : PSLThreeThreeFrattiniLifting.BinaryModuleBound) [IsSimpleGroup Q]
    {G : Type} [Group G] [Finite G] [Group.IsPerfect G]
    (pi : G →* Q) (hpi : Function.Surjective pi)
    (hR : IsPGroup 2 pi.ker) (hRΦ : pi.ker ≤ frattini G) (w : OuterWord) :
    ¬ ProductOrderCondition w 2 G :=
  not_condition_of_good_preimage pi hpi
    (PSLThreeThreeFrattiniLifting.preimage_Y13_good hmodule pi hpi hR hRΦ) w

end Kourovka2135.PSLThreeThreeOrderObstruction
