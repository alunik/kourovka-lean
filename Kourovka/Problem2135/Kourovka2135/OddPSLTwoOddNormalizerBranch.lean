import Kourovka2135.OddPSLTwoTetrahedralNormalizer
import Kourovka2135.OddPSLTwoLargeSplitGeneration
import Kourovka2135.OddPSLTwoSplitThreeFrattini
import Kourovka2135.OddNormalizerModelObstruction
import Kourovka2135.SLTwoRegularTraceConjugacy
import Kourovka2135.BinarySLTwoMinimalException

/-! Odd-prime noncentral least exceptions with an odd-field PSL2 quotient.

The projective tetrahedral element normalizes an actual binary four-group,
and the required second commutator is nonidentity. The broad trace good set
covers unit-group cardinal not dividing 24; the split-order-three set covers
the two small prime fields. No assumption on the radical prime relative to
the field characteristic is needed, and noncentrality remains explicit.
-/

set_option autoImplicit false
noncomputable section
universe u v

namespace Kourovka2135.OddPSLTwoOddNormalizerBranch

open SLTwoTetrahedralObstruction OddPSLTwoTetrahedralNormalizer
open OddPSLTwoProjectiveChart

variable {F : Type v} [Field F]

theorem tetrahedral_trace (x y : F) (hxy : x ^ 2 + y ^ 2 = -1)
    (h2 : (2 : F) ≠ 0) : (tetrahedral x y hxy h2).val.trace = -1 := by
  simp [tetrahedral, Matrix.trace_fin_two]
  field_simp
  ring

theorem tor_trace_of_order_three (r : Fˣ) (hr : orderOf r = 3) :
    (SLTwo.tor r).val.trace = -1 := by
  have hrne : (r : F) ≠ 1 := by
    intro h
    have he : r = 1 := Units.ext h
    rw [he, orderOf_one] at hr
    omega
  have hr3 : (r : F) ^ 3 = 1 := by
    exact congrArg Units.val (orderOf_dvd_iff_pow_eq_one.mp (by rw [hr]))
  have hpoly : (r : F) ^ 2 + (r : F) + 1 = 0 := by
    apply (mul_eq_zero.mp (show ((r : F) - 1) *
      ((r : F) ^ 2 + (r : F) + 1) = 0 by linear_combination hr3)).resolve_left
      (sub_ne_zero.mpr hrne)
  have ht : (SLTwo.tor r).val.trace = (r : F) + (r : F)⁻¹ := by
    simp [SLTwo.tor_val, Matrix.trace_fin_two]
  rw [ht]
  apply mul_left_cancel₀ r.ne_zero
  have hi := mul_inv_cancel₀ r.ne_zero
  linear_combination hpoly + hi

theorem tetrahedral_mem_splitOrderSet_three [Finite F]
    (hodd : Odd (Nat.card F)) (h3 : (3 : F) ≠ 0)
    (hsplit : 3 ∣ Nat.card F - 1)
    (x y : F) (hxy : x ^ 2 + y ^ 2 = -1) (h2 : (2 : F) ≠ 0) :
    tetrahedral x y hxy h2 ∈ BinarySplitTorusGoodPair.splitOrderSet 3 := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨r, hr⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) 3
    (by rwa [Nat.card_units])
  refine ⟨r, hr, ?_⟩
  apply SLTwoRegularTraceConjugacy.isConj_of_trace hodd
  · rw [tor_trace_of_order_three r hr, tetrahedral_trace x y hxy h2]
  · rw [tor_trace_of_order_three r hr]
    intro he
    apply h3
    linear_combination -he

end Kourovka2135.OddPSLTwoOddNormalizerBranch

namespace Kourovka2135

open OddPSLTwoProjectiveChart SLTwoTetrahedralObstruction OddPSLTwoTetrahedralNormalizer

/-- The uniform broad-set branch, including defining characteristic three. -/
theorem OrderMinimalException.false_of_odd_noncentral_odd_pslTwo_large
    {G : Type u} [Group G] [Finite G] {w : OuterWord} {p : ℕ}
    (h : OrderMinimalException w p G) (hp : p.Prime) (hoddp : p ≠ 2)
    (hnoncentral : ¬ solubleRadical G ≤ Subgroup.center G)
    (F : Type v) [Field F] [Finite F] (hodd : Odd (Nat.card F))
    (hcard : ¬ Nat.card Fˣ ∣ 24)
    (e : (G ⧸ solubleRadical G) ≃* Q F) : False := by
  have hsolv := proper_subgroups_solvable_of_equiv e
    (h.quotient_radical_proper_subgroup_isSolvable hp hnoncentral)
  have hgood := OddPSLTwoLargeSplitGeneration.projective_isGeneratingGoodSet F hodd hcard hsolv
  let : NeZero (ringChar F) := ⟨CharP.ringChar_ne_zero_of_finite F⟩
  obtain ⟨m, n, hmn⟩ := CharP.sq_add_sq F (ringChar F) (-1)
  have hxy : (m : F) ^ 2 + (n : F) ^ 2 = -1 := by
    simpa only [Int.cast_neg, Int.cast_one] using hmn
  have h2 := Ring.two_ne_zero (OddSLTwoCenter.ringChar_ne_two F hodd)
  let : IsElementaryAbelian 2 (fourGroup (m : F) (n : F) hxy) := fourGroup_elementary (m : F) (n : F) hxy
  exact h.false_of_odd_model_normalizer_good_set hp Nat.prime_two hoddp hoddp.symm
    hnoncentral e hgood (fourGroup (m : F) (n : F) hxy) (IsElementaryAbelian.isPGroup 2 _)
    (quotient F (tetrahedral (m : F) (n : F) hxy h2)) (quotient F quaternionI)
    (tetrahedral_projective_good (m : F) (n : F) hxy h2) (tetrahedral_normalizes (m : F) (n : F) hxy h2)
    (quaternionI_mem (m : F) (n : F) hxy) (conjugate_commutator_ne_one (m : F) (n : F) hxy h2)

/-- The small split-three branch; its good-set theorem also covers size seven. -/
theorem OrderMinimalException.false_of_odd_noncentral_odd_pslTwo_split_three
    {G : Type u} [Group G] [Finite G] {w : OuterWord} {p : ℕ}
    (h : OrderMinimalException w p G) (hp : p.Prime) (hoddp : p ≠ 2)
    (hnoncentral : ¬ solubleRadical G ≤ Subgroup.center G)
    (F : Type) [Field F] [Finite F] (hodd : Odd (Nat.card F))
    (h3 : (3 : F) ≠ 0) (hsplit : 3 ∣ Nat.card F - 1)
    (e : (G ⧸ solubleRadical G) ≃* Q F) : False := by
  have hsolv := proper_subgroups_solvable_of_equiv e
    (h.quotient_radical_proper_subgroup_isSolvable hp hnoncentral)
  have hgood := OddPSLTwoSplitThreeFrattini.projective_isGeneratingGoodSet F hsplit hsolv
  let : NeZero (ringChar F) := ⟨CharP.ringChar_ne_zero_of_finite F⟩
  obtain ⟨m, n, hmn⟩ := CharP.sq_add_sq F (ringChar F) (-1)
  have hxy : (m : F) ^ 2 + (n : F) ^ 2 = -1 := by
    simpa only [Int.cast_neg, Int.cast_one] using hmn
  have h2 := Ring.two_ne_zero (OddSLTwoCenter.ringChar_ne_two F hodd)
  let : IsElementaryAbelian 2 (fourGroup (m : F) (n : F) hxy) := fourGroup_elementary (m : F) (n : F) hxy
  apply h.false_of_odd_model_normalizer_good_set hp Nat.prime_two hoddp hoddp.symm
    hnoncentral e hgood (fourGroup (m : F) (n : F) hxy) (IsElementaryAbelian.isPGroup 2 _)
    (quotient F (tetrahedral (m : F) (n : F) hxy h2)) (quotient F quaternionI)
  · exact ⟨tetrahedral (m : F) (n : F) hxy h2,
      OddPSLTwoOddNormalizerBranch.tetrahedral_mem_splitOrderSet_three
        hodd h3 hsplit (m : F) (n : F) hxy h2, rfl⟩
  · exact tetrahedral_normalizes (m : F) (n : F) hxy h2
  · exact quaternionI_mem (m : F) (n : F) hxy
  · exact conjugate_commutator_ne_one (m : F) (n : F) hxy h2

theorem OrderMinimalException.false_of_odd_noncentral_odd_pslTwo_card_ge
    {G : Type u} [Group G] [Finite G] {w : OuterWord} {p : ℕ}
    (h : OrderMinimalException w p G) (hp : p.Prime) (hoddp : p ≠ 2)
    (hnoncentral : ¬ solubleRadical G ≤ Subgroup.center G)
    (F : Type v) [Field F] [Finite F] (hodd : Odd (Nat.card F))
    (hcard : 27 ≤ Nat.card F) (e : (G ⧸ solubleRadical G) ≃* Q F) : False :=
  h.false_of_odd_noncentral_odd_pslTwo_large hp hoddp hnoncentral F hodd
    (OddPSLTwoLargeSplitGeneration.card_units_not_dvd_twentyFour_of_ge F hcard) e

/-- Every prime parameter at least seven, without an unproved good-set premise. -/
theorem OrderMinimalException.false_of_odd_noncentral_prime_pslTwo_quotient
    {G : Type u} [Group G] [Finite G] {w : OuterWord} {p : ℕ}
    (h : OrderMinimalException w p G) (hp : p.Prime) (hoddp : p ≠ 2)
    (hnoncentral : ¬ solubleRadical G ≤ Subgroup.center G)
    (F : Type) [Field F] [Finite F]
    (hprime : (Nat.card F).Prime) (hsize : 7 ≤ Nat.card F)
    (e : (G ⧸ solubleRadical G) ≃* Q F) : False := by
  have hodd := hprime.odd_of_ne_two (by omega)
  by_cases hsmall : Nat.card F = 7 ∨ Nat.card F = 13
  · let : Fintype F := Fintype.ofFinite F
    let : Fact (Nat.card F).Prime := ⟨hprime⟩
    let : CharP F (Nat.card F) := charP_of_card_eq_prime (by simp [Nat.card_eq_fintype_card])
    have h3 : (3 : F) ≠ 0 := by
      intro he
      have hd := (CharP.cast_eq_zero_iff F (Nat.card F) 3).mp he
      exact (Nat.not_dvd_of_pos_of_lt (by decide : 0 < 3) (by omega : 3 < Nat.card F)) hd
    have hsplit : 3 ∣ Nat.card F - 1 := by
      rcases hsmall with h7 | h13
      · rw [h7]
        decide
      · rw [h13]
        decide
    exact h.false_of_odd_noncentral_odd_pslTwo_split_three hp hoddp hnoncentral F hodd h3 hsplit e
  · have hcard : ¬ Nat.card Fˣ ∣ 24 := by
      intro hd
      rw [Nat.card_units] at hd
      have hl := Nat.le_of_dvd (by decide : 0 < 24) hd
      have hu : Nat.card F ≤ 25 := by omega
      interval_cases hq : Nat.card F <;> norm_num at *
    exact h.false_of_odd_noncentral_odd_pslTwo_large hp hoddp hnoncentral F hodd hcard e

end Kourovka2135
