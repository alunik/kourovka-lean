import Kourovka2135.SuzukiRootNormalizer
import Kourovka2135.BinarySplitGoodSetObstruction

/-! Any odd persistent value with a nontrivial Suzuki split-torus image
contradicts the binary order condition across an actual binary kernel. -/

set_option autoImplicit false
noncomputable section
namespace Kourovka2135.SuzukiBinaryGoodSetObstruction

open SuzukiTorusMovingRank SuzukiRootNormalizer

variable {E : Type*} [Group E]

theorem false_of_odd_derived_value_torus_image
    (m : ℕ) (pi : E →* G m) (hpi : Function.Surjective pi)
    (hker : IsPGroup 2 pi.ker) (k : ℕ)
    (h : ProductOrderCondition (OuterWord.derivedWord k) 2 E)
    (x : E) (hx : x ∈ (OuterWord.derivedWord k).values E)
    (hodd : Odd (orderOf x)) (u : (K m)ˣ) (hu : u ≠ 1)
    (himage : IsConj (torusHom m u) (pi x)) : False := by
  obtain ⟨s, hs⟩ := isConj_iff.mp himage
  obtain ⟨z, hz⟩ := hpi s
  let y := z⁻¹ * x * z
  have hy : y ∈ (OuterWord.derivedWord k).values E :=
    (OuterWord.derivedWord k).conj_mem_values hx z
  have hyorder : orderOf y = orderOf x := by
    simpa only [y, MulAut.conj_apply, inv_inv] using (MulAut.conj z⁻¹).orderOf_eq x
  have hyp : ¬ 2 ∣ orderOf y := by
    rw [hyorder]
    exact hodd.not_two_dvd_nat
  have hiy : pi y = torusHom m u := by
    change pi (z⁻¹ * x * z) = torusHom m u
    rw [map_mul, map_mul, map_inv, hz, ← hs]
    group
  let P := (U m).comap pi
  have hP : IsPGroup 2 P := (isPGroup_U m).comap_of_ker_isPGroup pi hker
  have hyn : y ∈ Subgroup.normalizer P := by
    apply (U m).le_normalizer_comap pi
    change pi y ∈ Subgroup.normalizer (U m)
    rw [hiy]
    exact torus_normalizes_U m u
  have hcentral := h.derivedValue_centralizes_pSubgroup Nat.prime_two P hP hy hyp hyn
  have hc : Commute (rootZero m 1) (torusHom m u) := by
    rw [← hiy]
    exact BinarySplitGoodSetObstruction.centralizes_of_centralizes_comap pi hpi (U m) y
      hcentral (rootZero m 1) ((mem_U_iff m _).mpr ⟨1, rfl⟩)
  exact hu (torus_eq_one_of_commute_rootZero m u 1 one_ne_zero hc.symm)

end Kourovka2135.SuzukiBinaryGoodSetObstruction
