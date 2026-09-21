import Kourovka2135.OddGeneratingGoodSet
import Kourovka2135.DerivedCentralization
import Kourovka2135.BinarySplitTorusGoodPair

/-! A binary-kernel quotient with an odd generating good set over a nonidentity
split-torus set cannot satisfy the product-order condition. The actual root
subgroup is a 2-group, its preimage remains a 2-group, and derived-value
centralization contradicts the concrete torus action on uni(1). No radical
noncentrality, perfection, Frattini condition, or classification is assumed.
-/

set_option autoImplicit false
noncomputable section
universe u v

namespace Kourovka2135.BinarySplitGoodSetObstruction

section Descent
variable {G : Type u} {H : Type v} [Group G] [Group H]

/-- Centralization of the full preimage descends along an actual surjection. -/
theorem centralizes_of_centralizes_comap (pi : G →* H)
    (hpi : Function.Surjective pi) (P : Subgroup H) (x : G)
    (hx : ∀ y ∈ P.comap pi, Commute y x) :
    ∀ y ∈ P, Commute y (pi x) := by
  intro y hy
  obtain ⟨z, rfl⟩ := hpi y
  exact (hx z hy).map pi
end Descent

section BinaryRoot
variable {F : Type v} [Field F] [CharP F 2]

/-- The actual unipotent root subgroup is a 2-group, even over an infinite field. -/
theorem unip_isPGroup : IsPGroup 2 (SLTwo.Unip F) := by
  have hF : IsPGroup 2 (Multiplicative F) := by
    intro x
    refine ⟨1, ?_⟩
    apply Multiplicative.toAdd.injective
    change 2 • x.toAdd = 0
    simp only [two_nsmul, CharTwo.add_self_eq_zero]
  exact hF.of_surjective (SLTwo.uniHom F).rangeRestrict
    (SLTwo.uniHom F).rangeRestrict_surjective

/-- In characteristic two only the identity torus parameter centralizes uni(1). -/
theorem tor_parameter_eq_one_of_commute (u : Fˣ)
    (h : Commute (SLTwo.tor u) (SLTwo.uni (1 : F))) : u = 1 := by
  have heq : SLTwo.uni ((u : F) ^ 2 * 1) = SLTwo.uni (1 : F) := by
    rw [← SLTwo.tor_conj_uni, h.eq, mul_assoc, mul_inv_cancel, mul_one]
  have hparam : (Multiplicative.ofAdd ((u : F) ^ 2 * 1) : Multiplicative F) =
      Multiplicative.ofAdd (1 : F) := SLTwo.uniHom_injective (K := F) heq
  have hsq : (u : F) ^ 2 = 1 := by
    have hh : (u : F) ^ 2 * 1 = 1 := congrArg Multiplicative.toAdd hparam
    simpa only [mul_one] using hh
  have hu : (u : F) = 1 := by
    simpa only [CharTwo.neg_eq, or_self] using sq_eq_one_iff.mp hsq
  exact Units.ext hu
end BinaryRoot

section Obstruction
variable {G : Type u} [Group G]
variable {F : Type v} [Field F] [CharP F 2]

/-- An odd derived value cannot have a nonidentity split-torus image when the
actual quotient kernel is a 2-group. No finiteness hypothesis is needed. -/
theorem false_of_odd_derived_value_split_image
    (pi : G →* SLTwo.SL2 F) (hpi : Function.Surjective pi)
    (hker : IsPGroup 2 pi.ker) (k : ℕ)
    (h : ProductOrderCondition (OuterWord.derivedWord k) 2 G)
    (x : G) (hx : x ∈ (OuterWord.derivedWord k).values G)
    (hodd : Odd (orderOf x)) (u : Fˣ) (hu : u ≠ 1)
    (himage : IsConj (SLTwo.tor u) (pi x)) : False := by
  obtain ⟨s, hs⟩ := isConj_iff.mp himage
  obtain ⟨z, hz⟩ := hpi s
  let y := z⁻¹ * x * z
  have hy : y ∈ (OuterWord.derivedWord k).values G :=
    (OuterWord.derivedWord k).conj_mem_values hx z
  have hyorder : orderOf y = orderOf x := by
    simpa only [y, MulAut.conj_apply, inv_inv] using (MulAut.conj z⁻¹).orderOf_eq x
  have hyp : ¬ 2 ∣ orderOf y := by
    rw [hyorder]
    exact hodd.not_two_dvd_nat
  have hiy : pi y = SLTwo.tor u := by
    change pi (z⁻¹ * x * z) = SLTwo.tor u
    rw [map_mul, map_mul, map_inv, hz, ← hs]
    group
  let P := (SLTwo.Unip F).comap pi
  have hP : IsPGroup 2 P := unip_isPGroup.comap_of_ker_isPGroup pi hker
  have hyn : y ∈ Subgroup.normalizer P := by
    apply (SLTwo.Unip F).le_normalizer_comap pi
    change pi y ∈ Subgroup.normalizer (SLTwo.Unip F)
    rw [hiy]
    exact SLTwo.torus_le_normalizer ⟨u, rfl⟩
  have hcentral := h.derivedValue_centralizes_pSubgroup Nat.prime_two P hP hy hyp hyn
  have hc : Commute (SLTwo.uni (1 : F)) (SLTwo.tor u) := by
    rw [← hiy]
    exact centralizes_of_centralizes_comap pi hpi (SLTwo.Unip F) y hcentral
      (SLTwo.uni (1 : F)) ((SLTwo.mem_Unip_iff _).mpr ⟨1, rfl⟩)
  exact hu (tor_parameter_eq_one_of_commute u hc.symm)

/-- The actual odd generating-good-set invariant rules out the product-order
condition for every outer word, including the leaf. The prime is used only
to ensure that the allowed split-torus parameter is nonidentity. -/
theorem not_productOrderCondition
    (pi : G →* SLTwo.SL2 F) (hpi : Function.Surjective pi)
    (hker : IsPGroup 2 pi.ker) (r : ℕ) (hr : r.Prime)
    (hgood : HasOddGeneratingGoodSetOver pi
      (BinarySplitTorusGoodPair.splitOrderSet (F := F) r)) (w : OuterWord) :
    ¬ ProductOrderCondition w 2 G := by
  intro h
  obtain ⟨x, hx, hxB, hxodd⟩ := hgood.exists_value (OuterWord.derivedWord w.height)
  obtain ⟨u, huorder, huconj⟩ := hxB
  have hu : u ≠ 1 := by
    intro heq
    exact hr.ne_one (by simpa only [heq, orderOf_one] using huorder.symm)
  have hd : ProductOrderCondition (OuterWord.derivedWord w.height) 2 G := by
    intro a ha b hb hap hbp
    exact h a (w.derivedWord_values_subset w.height le_rfl ha)
      b (w.derivedWord_values_subset w.height le_rfl hb) hap hbp
  exact false_of_odd_derived_value_split_image pi hpi hker w.height hd x hx hxodd
    u hu huconj

end Obstruction
end Kourovka2135.BinarySplitGoodSetObstruction
