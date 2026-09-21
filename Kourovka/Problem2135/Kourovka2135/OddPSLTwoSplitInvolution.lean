import Kourovka2135.OddPSLTwoSplitCentralizer

/-! Actual conjugacy of projective involutions when minus one is a square.

A noncentral lift whose square is central has trace zero. Two explicit
rational fixed points then reduce conjugacy to the checked ordered-pair
transitivity and diagonal decomposition. No classification, eigenbasis
normalization, or finiteness assumption is used.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.OddPSLTwoSplitInvolution

open OddPSLTwoProjectiveChart OddPSLTwoTorusMovingRank
open OddPSLTwoSplitDihedral OddPSLTwoSplitCentralizer
open scoped Matrix LinearAlgebra.Projectivization IsMulCommutative

variable (F : Type*) [Field F]

theorem trace_zero_of_square_central (A : SLTwo.SL2 F)
    (hsq : A ^ 2 ∈ Subgroup.center (SLTwo.SL2 F))
    (hne : A ∉ Subgroup.center (SLTwo.SL2 F)) :
    A.val 0 0 + A.val 1 1 = 0 := by
  obtain ⟨z, _, hz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hsq
  have h01 : A.val 0 0 * A.val 0 1 + A.val 0 1 * A.val 1 1 = 0 := by
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 0 1) hz
    simpa [pow_two, Matrix.mul_apply, Fin.sum_univ_two] using h.symm
  have h10 : A.val 1 0 * A.val 0 0 + A.val 1 1 * A.val 1 0 = 0 := by
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 1 0) hz
    simpa [pow_two, Matrix.mul_apply, Fin.sum_univ_two] using h.symm
  have h00 : A.val 0 0 * A.val 0 0 + A.val 0 1 * A.val 1 0 = z := by
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 0 0) hz
    simpa [pow_two, Matrix.mul_apply, Fin.sum_univ_two] using h.symm
  have h11 : A.val 1 0 * A.val 0 1 + A.val 1 1 * A.val 1 1 = z := by
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 1 1) hz
    simpa [pow_two, Matrix.mul_apply, Fin.sum_univ_two] using h.symm
  by_contra ht
  have hb : A.val 0 1 = 0 := by
    apply (mul_eq_zero.mp (show A.val 0 1 * (A.val 0 0 + A.val 1 1) = 0 by
      linear_combination h01)).resolve_right ht
  have hc : A.val 1 0 = 0 := by
    apply (mul_eq_zero.mp (show A.val 1 0 * (A.val 0 0 + A.val 1 1) = 0 by
      linear_combination h10)).resolve_right ht
  have hd : A.val 0 0 = A.val 1 1 := by
    apply sub_eq_zero.mp
    exact (mul_eq_zero.mp (show (A.val 0 0 - A.val 1 1) *
      (A.val 0 0 + A.val 1 1) = 0 by linear_combination h00 - h11)).resolve_right ht
  have hdet : A.val 0 0 * A.val 1 1 - A.val 0 1 * A.val 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using A.det_coe
  apply hne
  apply Matrix.SpecialLinearGroup.mem_center_iff.mpr
  refine ⟨A.val 0 0, ?_, ?_⟩
  · simpa only [Fintype.card_fin, pow_two, ← hd, hb, hc, zero_mul, sub_zero] using hdet
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.scalar, hb, hc, hd]

theorem quotient_fixed_of_mulVec (A : SLTwo.SL2 F) (x : Option F) (t : F)
    (h : A.val.mulVec (representative F x) = t • representative F x) :
    quotient F A • x = x := by
  apply point_injective F
  rw [point_smul]
  change Projectivization.mk F (A.val.mulVec (representative F x)) _ =
    Projectivization.mk F (representative F x) _
  exact (Projectivization.mk_eq_mk_iff' F _ _ _ _).mpr ⟨t, h.symm⟩

/-- The two fixed points are explicit affine roots if the lower-left entry
is nonzero; otherwise one is infinity. -/
theorem exists_two_fixed_of_trace_zero (A : SLTwo.SL2 F)
    (ht : A.val 0 0 + A.val 1 1 = 0) (i : Fˣ)
    (hi : (i : F) ^ 2 = -1) (hine : (i : F) ^ 2 ≠ 1) :
    ∃ x y : Option F, x ≠ y ∧ quotient F A • x = x ∧ quotient F A • y = y := by
  have htwo : (2 : F) ≠ 0 := by
    intro h
    apply hine
    calc
      (i : F) ^ 2 = -1 := hi
      _ = 1 := by linear_combination -h
  have hd : A.val 1 1 = -A.val 0 0 := by linear_combination ht
  have hdet : A.val 0 0 * A.val 1 1 - A.val 0 1 * A.val 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using A.det_coe
  have he : A.val 0 0 ^ 2 + A.val 0 1 * A.val 1 0 = -1 := by
    rw [hd] at hdet
    linear_combination -hdet
  by_cases hc : A.val 1 0 = 0
  · have ha : A.val 0 0 ≠ 0 := by
      intro h
      rw [h, hc, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_add] at he
      exact neg_ne_zero.mpr one_ne_zero he.symm
    have hden : 2 * A.val 0 0 ≠ 0 := mul_ne_zero htwo ha
    refine ⟨none, some (-A.val 0 1 / (2 * A.val 0 0)), (by simp), ?_, ?_⟩
    · apply quotient_fixed_of_mulVec F A none (A.val 0 0)
      ext j
      fin_cases j <;> simp [representative, Matrix.mulVec, dotProduct, Fin.sum_univ_two, hc]
    · apply quotient_fixed_of_mulVec F A _ (-A.val 0 0)
      ext j
      fin_cases j
      · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
        change A.val 0 0 * (-A.val 0 1 / (2 * A.val 0 0)) + A.val 0 1 * 1 =
          -A.val 0 0 * (-A.val 0 1 / (2 * A.val 0 0))
        field_simp [hden]
        ring
      · simp [representative, Matrix.mulVec, dotProduct, Fin.sum_univ_two, hc, hd]
  · let x : F := (A.val 0 0 + (i : F)) / A.val 1 0
    let y : F := (A.val 0 0 - (i : F)) / A.val 1 0
    have hxy : x ≠ y := by
      intro h
      have hh : A.val 0 0 + (i : F) = A.val 0 0 - (i : F) :=
        (div_left_inj' hc).mp h
      have hzero : (2 : F) * (i : F) = 0 := by linear_combination hh
      exact mul_ne_zero htwo i.ne_zero hzero
    refine ⟨some x, some y, fun h => hxy (Option.some.inj h), ?_, ?_⟩
    · apply quotient_fixed_of_mulVec F A (some x) (i : F)
      ext j
      fin_cases j
      · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
        change A.val 0 0 * x + A.val 0 1 * 1 = (i : F) * x
        dsimp [x]
        field_simp [hc]
        linear_combination he - hi
      · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
        change A.val 1 0 * x + A.val 1 1 * 1 = (i : F) * 1
        dsimp [x]
        field_simp [hc]
        linear_combination ht
    · apply quotient_fixed_of_mulVec F A (some y) (-(i : F))
      ext j
      fin_cases j
      · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
        change A.val 0 0 * y + A.val 0 1 * 1 = -(i : F) * y
        dsimp [y]
        field_simp [hc]
        linear_combination he - hi
      · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
        change A.val 1 0 * y + A.val 1 1 * 1 = -(i : F) * 1
        dsimp [y]
        field_simp [hc]
        linear_combination ht

/-- Every actual nonidentity projective involution is conjugate to the
specified split torus involution when minus one has the specified root. -/
theorem exists_conjugator_split_involution (i : Fˣ)
    (hi : (i : F) ^ 2 = -1) (hine : (i : F) ^ 2 ≠ 1)
    (g : Q F) (hg : g ≠ 1) (hsq : g ^ 2 = 1) :
    ∃ a : Q F, a * g * a⁻¹ = projectiveTorusHom F i := by
  obtain ⟨A, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center (SLTwo.SL2 F)) g
  change quotient F A ≠ 1 at hg
  change (quotient F A) ^ 2 = 1 at hsq
  have hAc : A ^ 2 ∈ Subgroup.center (SLTwo.SL2 F) := by
    apply (QuotientGroup.eq_one_iff _).mp
    change quotient F (A ^ 2) = 1
    rw [map_pow]
    exact hsq
  have hAn : A ∉ Subgroup.center (SLTwo.SL2 F) := by
    intro h
    exact hg ((QuotientGroup.eq_one_iff _).mpr h)
  obtain ⟨x, y, hxy, hx, hy⟩ := exists_two_fixed_of_trace_zero F A
    (trace_zero_of_square_central F A hAc hAn) i hi hine
  obtain ⟨a, hax, hay⟩ := exists_pair_to_base F hxy
  have hconj (z : Option F) (hz : quotient F A • z = z) :
      (a * quotient F A * a⁻¹) • (a • z) = a • z := by
    rw [mul_smul, mul_smul, inv_smul_smul, hz]
  obtain ⟨r, hr⟩ := exists_torus_of_fixed F (a * quotient F A * a⁻¹)
    (by simpa only [hax] using hconj x hx) (by simpa only [hay] using hconj y hy)
  have hr_sq : (projectiveTorusHom F r) ^ 2 = 1 := by
    rw [← hr]
    calc
      _ = a * (quotient F A) ^ 2 * a⁻¹ := by simp only [pow_two]; group
      _ = 1 := by rw [hsq]; group
  rcases (torus_sq_eq_one_iff F i r hi).mp hr_sq with h | h
  · exfalso
    apply hg
    have he := hr.trans h
    calc
      quotient F A = a⁻¹ * (a * quotient F A * a⁻¹) * a := by group
      _ = 1 := by rw [he]; group
  · exact ⟨a, hr.trans h⟩

/-- The unconditional elementary-abelian bound over a field with a
specified square root of minus one, distinct from a square root of one. -/
theorem card_elementary_two_le_four (E : Subgroup (Q F)) [IsElementaryAbelian 2 E]
    (i : Fˣ) (hi : (i : F) ^ 2 = -1) (hine : (i : F) ^ 2 ≠ 1) :
    Nat.card E ≤ 4 := by
  classical
  by_cases hE : E = ⊥
  · simp [hE]
  obtain ⟨g, hg⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hE
  have hgne : (g : Q F) ≠ 1 := fun h => hg (Subtype.ext h)
  obtain ⟨a, ha⟩ := exists_conjugator_split_involution F i hi hine g hgne
    (elemPow_eq_one_of_isElementaryAbelian (g : Q F) g.property)
  let f : Q F →* Q F := (MulAut.conj a).toMonoidHom
  let E' : Subgroup (Q F) := E.map f
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : IsElementaryAbelian 2 E' := IsElementaryAbelian.map f
  have hiE : projectiveTorusHom F i ∈ E' := by
    refine Subgroup.mem_map.mpr ⟨g, g.property, ?_⟩
    exact ha
  have hb := OddPSLTwoSplitCentralizer.card_elementary_two_le_four F E' i hi hine hiE
  have hc : Nat.card E' = Nat.card E := Subgroup.card_map_of_injective (MulAut.conj a).injective
  exact hc ▸ hb

theorem card_elementary_two_in_torus_le_two (E : Subgroup (Q F))
    [IsElementaryAbelian 2 E] (i : Fˣ) (hi : (i : F) ^ 2 = -1)
    (hE : E ≤ (projectiveTorusHom F).range) : Nat.card E ≤ 2 := by
  classical
  by_cases hiE : projectiveTorusHom F i ∈ E
  · let f : Fin 2 → E := ![1, ⟨projectiveTorusHom F i, hiE⟩]
    have hf : Function.Surjective f := by
      intro g
      obtain ⟨r, hr⟩ := hE g.property
      have hp : (projectiveTorusHom F r) ^ 2 = 1 := by
        rw [hr]
        exact elemPow_eq_one_of_isElementaryAbelian (g : Q F) g.property
      rcases (torus_sq_eq_one_iff F i r hi).mp hp with h | h
      · exact ⟨0, Subtype.ext (h.symm.trans hr)⟩
      · exact ⟨1, Subtype.ext (h.symm.trans hr)⟩
    simpa only [Nat.card_fin] using Nat.card_le_card_of_surjective f hf
  · have hb : E = ⊥ := by
      apply le_antisymm ?_ bot_le
      intro g hg
      change g = 1
      obtain ⟨r, hr⟩ := hE hg
      have hp : (projectiveTorusHom F r) ^ 2 = 1 := by
        rw [hr]
        exact elemPow_eq_one_of_isElementaryAbelian g hg
      rcases (torus_sq_eq_one_iff F i r hi).mp hp with h | h
      · exact hr.symm.trans h
      · exact (hiE ((hr.symm.trans h) ▸ hg)).elim
    simp [hb]

/-- Any elementary abelian subgroup of order four is self-centralizing
under the same square-root hypothesis, with no chosen involution premise. -/
theorem centralizer_elementary_four_eq_self (E : Subgroup (Q F))
    [IsElementaryAbelian 2 E] (hcard : Nat.card E = 4)
    (i : Fˣ) (hi : (i : F) ^ 2 = -1) (hine : (i : F) ^ 2 ≠ 1) :
    Subgroup.centralizer (E : Set (Q F)) = E := by
  classical
  have hE : E ≠ ⊥ := by intro h; simp [h] at hcard
  obtain ⟨g, hg⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hE
  have hgne : (g : Q F) ≠ 1 := fun h => hg (Subtype.ext h)
  obtain ⟨a, ha⟩ := exists_conjugator_split_involution F i hi hine g hgne
    (elemPow_eq_one_of_isElementaryAbelian (g : Q F) g.property)
  let f : Q F →* Q F := (MulAut.conj a).toMonoidHom
  let E' : Subgroup (Q F) := E.map f
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : IsElementaryAbelian 2 E' := IsElementaryAbelian.map f
  have hiE : projectiveTorusHom F i ∈ E' :=
    Subgroup.mem_map.mpr ⟨g, g.property, ha⟩
  have hc : Nat.card E' = 4 :=
    (Subgroup.card_map_of_injective (MulAut.conj a).injective).trans hcard
  have hnle : ¬ E' ≤ (projectiveTorusHom F).range := by
    intro h
    have hb := card_elementary_two_in_torus_le_two F E' i hi h
    omega
  change ¬ (E' : Set (Q F)) ⊆ ((projectiveTorusHom F).range : Set (Q F)) at hnle
  obtain ⟨b, hb, hbout⟩ := Set.not_subset.mp hnle
  have hC := centralizer_eq_self_of_split_involution F E' i hi hine hiE b hb hbout
  apply le_antisymm
  · intro x hx
    have hfx : f x ∈ Subgroup.centralizer (E' : Set (Q F)) := by
      apply Subgroup.mem_centralizer_iff.mpr
      intro y hy
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
      rw [← map_mul, ← map_mul, (Subgroup.mem_centralizer_iff.mp hx) z hz]
    rw [hC] at hfx
    exact (Subgroup.mem_map_iff_mem (MulAut.conj a).injective).mp hfx
  · intro x hx
    apply Subgroup.mem_centralizer_iff.mpr
    intro y hy
    exact setLike_mul_comm hy hx

end Kourovka2135.OddPSLTwoSplitInvolution
