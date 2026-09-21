import Kourovka2135.OddPSLTwoSplitInvolution
import Kourovka2135.SmallNormalTwoAction
import Kourovka2135.OddSLTwoCenter
import Kourovka2135.CentralPGroupOddLift
import Kourovka2135.CoprimePGroupLift
import Kourovka2135.Vendor.CFSG.ChiefFactors.Core
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

/-! Soluble overgroups of a large split binary torus in actual PSL2.

The field-unit group is a 2-group. A soluble overgroup has a nontrivial
elementary abelian normal subgroup. Odd elementary abelian subgroups have
a unique fixed coordinate point; binary ones have order at most four,
and the order-four case is incompatible with the large torus element.
The proof uses the actual projective action and matrix multiplication,
not a subgroup-classification theorem.

This source is a draft until its first strict compile and ownership audit.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.OddPSLTwoFermatOvergroup

open OddPSLTwoProjectiveChart OddPSLTwoTorusMovingRank
open OddPSLTwoSplitDihedral OddPSLTwoSplitCentralizer
open scoped Matrix LinearAlgebra.Projectivization IsMulCommutative

section GroupLemmas

variable {G K : Type*} [Group G] [Group K]

theorem eq_one_of_binary_odd (hG : IsPGroup 2 G) (g : G)
    (hg : Odd (orderOf g)) : g = 1 := by
  obtain ⟨n, hn⟩ := hG.exists_orderOf_dvd_pow g
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
    (hg.coprime_two_right.pow_right n) dvd_rfl hn)

/-- Commuting images lift to actual commutation when the second lift has
odd order and the actual kernel is central and binary. -/
theorem commute_of_odd_map_commute (f : G →* K)
    (hc : f.ker ≤ Subgroup.center G) (hker : IsPGroup 2 f.ker)
    (x y : G) (hy : Odd (orderOf y)) (hxy : Commute (f x) (f y)) :
    Commute x y := by
  have he : x * y * x⁻¹ = y := by
    apply CentralPGroupOddLift.eq_of_odd_orderOf f hc hker
    · rw [map_mul, map_mul, map_inv, hxy.eq, mul_inv_cancel_right]
    · simpa only [← MulAut.conj_apply, MulEquiv.orderOf_eq] using hy
    · exact hy
  exact mul_inv_eq_iff_eq_mul.mp he

/-- A commuting normal subgroup containing an element with a unique
fixed point forces the whole group to fix that point. -/
theorem fixed_of_normal_unique {X : Type*} [MulAction G X]
    (E : Subgroup G) [E.Normal] [IsMulCommutative E]
    (e : E) (x : X) (hfix : ∀ y : X, (e : G) • y = y ↔ y = x) :
    ∀ g : G, g • x = x := by
  have hex : (e : G) • x = x := (hfix x).mpr rfl
  have hEfix (z : E) : (z : G) • x = x := by
    apply (hfix _).mp
    have hc : (e : G) * z = (z : G) * e :=
      congrArg E.subtype (mul_comm e z)
    rw [← mul_smul, hc, mul_smul, hex]
  intro g
  let z : E := ⟨g⁻¹ * e * g,
    by simpa only [inv_inv] using
      (inferInstance : E.Normal).conj_mem (e : G) e.property g⁻¹⟩
  apply (hfix _).mp
  calc
    (e : G) • (g • x) = g • ((z : G) • x) := by
      simp only [← mul_smul]
      congr 1
      dsimp [z]
      group
    _ = g • x := congrArg (fun y => g • y) (hEfix z)

end GroupLemmas

variable (F : Type*) [Field F]

theorem torus_conjugate_matrix (s : Fˣ) (A : SLTwo.SL2 F) :
    (SLTwo.tor s * A * (SLTwo.tor s)⁻¹).val =
      !![A.val 0 0, (s : F) ^ 2 * A.val 0 1;
        ((s : F)⁻¹) ^ 2 * A.val 1 0, A.val 1 1] := by
  rw [SLTwo.tor_inv]
  change ((SLTwo.tor s).val * A.val) * (SLTwo.tor s⁻¹).val = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SLTwo.tor, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_two, pow_two, mul_assoc, mul_comm]

/-- Commuting with a sufficiently noncentral torus conjugate forces a
matrix to be diagonal or scalar plus one nonzero root entry. -/
theorem diagonal_or_root_of_commute_torus_conjugate (s : Fˣ)
    (hs : (s : F) ^ 4 ≠ 1) (A : SLTwo.SL2 F)
    (hc : Commute A (SLTwo.tor s * A * (SLTwo.tor s)⁻¹)) :
    (A.val 0 1 = 0 ∧ A.val 1 0 = 0) ∨
    (A.val 1 0 = 0 ∧ A.val 0 0 = A.val 1 1 ∧ A.val 0 1 ≠ 0) ∨
    (A.val 0 1 = 0 ∧ A.val 0 0 = A.val 1 1 ∧ A.val 1 0 ≠ 0) := by
  have hs2 : (s : F) ^ 2 ≠ 1 := by
    intro h
    apply hs
    calc
      (s : F) ^ 4 = ((s : F) ^ 2) ^ 2 := by ring
      _ = 1 := by rw [h, one_pow]
  have he := congrArg Subtype.val hc.eq
  change A.val * (SLTwo.tor s * A * (SLTwo.tor s)⁻¹).val =
    (SLTwo.tor s * A * (SLTwo.tor s)⁻¹).val * A.val at he
  rw [torus_conjugate_matrix] at he
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 0 0) he
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 0 1) he
  have h10 := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 1 0) he
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10
  change A.val 0 0 * A.val 0 0 +
    A.val 0 1 * ((s : F)⁻¹ ^ 2 * A.val 1 0) =
    A.val 0 0 * A.val 0 0 + ((s : F) ^ 2 * A.val 0 1) * A.val 1 0 at h00
  change A.val 0 0 * ((s : F) ^ 2 * A.val 0 1) + A.val 0 1 * A.val 1 1 =
    A.val 0 0 * A.val 0 1 + ((s : F) ^ 2 * A.val 0 1) * A.val 1 1 at h01
  change A.val 1 0 * A.val 0 0 + A.val 1 1 * ((s : F)⁻¹ ^ 2 * A.val 1 0) =
    ((s : F)⁻¹ ^ 2 * A.val 1 0) * A.val 0 0 + A.val 1 1 * A.val 1 0 at h10
  have hbc : A.val 0 1 * A.val 1 0 * ((s : F) ^ 4 - 1) = 0 := by
    field_simp [s.ne_zero] at h00
    linear_combination -h00
  have hb : A.val 0 1 * (A.val 0 0 - A.val 1 1) * ((s : F) ^ 2 - 1) = 0 := by
    linear_combination h01
  have hd : A.val 1 0 * (A.val 0 0 - A.val 1 1) * ((s : F) ^ 2 - 1) = 0 := by
    field_simp [s.ne_zero] at h10
    linear_combination h10
  have hbc0 : A.val 0 1 * A.val 1 0 = 0 :=
    (mul_eq_zero.mp hbc).resolve_right (sub_ne_zero.mpr hs)
  have hb0 : A.val 0 1 * (A.val 0 0 - A.val 1 1) = 0 :=
    (mul_eq_zero.mp hb).resolve_right (sub_ne_zero.mpr hs2)
  have hc0 : A.val 1 0 * (A.val 0 0 - A.val 1 1) = 0 :=
    (mul_eq_zero.mp hd).resolve_right (sub_ne_zero.mpr hs2)
  by_cases h01 : A.val 0 1 = 0
  · by_cases h10 : A.val 1 0 = 0
    · exact Or.inl ⟨h01, h10⟩
    · exact Or.inr (Or.inr ⟨h01,
        sub_eq_zero.mp ((mul_eq_zero.mp hc0).resolve_left h10), h10⟩)
  · exact Or.inr (Or.inl ⟨(mul_eq_zero.mp hbc0).resolve_left h01,
      sub_eq_zero.mp ((mul_eq_zero.mp hb0).resolve_left h01), h01⟩)

theorem eq_torus_of_diagonal (A : SLTwo.SL2 F)
    (hb : A.val 0 1 = 0) (hc : A.val 1 0 = 0) :
    ∃ r : Fˣ, A = SLTwo.tor r := by
  have hd : A.val 0 0 * A.val 1 1 = 1 := by
    simpa only [Matrix.det_fin_two, hb, hc, zero_mul, sub_zero] using A.det_coe
  have ha : A.val 0 0 ≠ 0 := by intro h; rw [h, zero_mul] at hd; exact zero_ne_one hd
  have h11 : A.val 1 1 = (A.val 0 0)⁻¹ := by
    apply mul_left_cancel₀ ha
    rw [hd, mul_inv_cancel₀ ha]
  refine ⟨Units.mk0 (A.val 0 0) ha, ?_⟩
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [SLTwo.tor, hb, hc, h11]

theorem upper_unique_fixed (A : SLTwo.SL2 F) (hc : A.val 1 0 = 0)
    (hd : A.val 0 0 = A.val 1 1) (hb : A.val 0 1 ≠ 0) (x : Option F) :
    quotient F A • x = x ↔ x = none := by
  cases x with
  | none =>
      refine ⟨fun _ => rfl, fun _ => ?_⟩
      apply OddPSLTwoSplitInvolution.quotient_fixed_of_mulVec F A none (A.val 0 0)
      ext j
      fin_cases j <;> simp [representative, Matrix.mulVec, dotProduct,
        Fin.sum_univ_two, hc]
  | some x =>
      constructor
      · intro h
        have he := congrArg (point F) h
        rw [point_smul] at he
        obtain ⟨t, ht⟩ := (Projectivization.mk_eq_mk_iff' F _ _ _ _).mp he
        change t • representative F (some x) = A.val.mulVec (representative F (some x)) at ht
        have h0 := congrFun ht 0
        have h1 := congrFun ht 1
        simp [representative, Matrix.mulVec, dotProduct, Fin.sum_univ_two, hc] at h0 h1
        exfalso
        apply hb
        linear_combination -h0 + x * h1 - x * hd
      · intro h
        cases h

theorem lower_unique_fixed (A : SLTwo.SL2 F) (hb : A.val 0 1 = 0)
    (hd : A.val 0 0 = A.val 1 1) (hc : A.val 1 0 ≠ 0) (x : Option F) :
    quotient F A • x = x ↔ x = some 0 := by
  cases x with
  | none =>
      constructor
      · intro h
        exact (hc (OddPSLTwoBorel.lowerLeft_eq_zero F A h)).elim
      · intro h
        cases h
  | some x =>
      constructor
      · intro h
        have he := congrArg (point F) h
        rw [point_smul] at he
        obtain ⟨t, ht⟩ := (Projectivization.mk_eq_mk_iff' F _ _ _ _).mp he
        change t • representative F (some x) = A.val.mulVec (representative F (some x)) at ht
        have h0 := congrFun ht 0
        have h1 := congrFun ht 1
        simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct,
          Fin.sum_univ_two] at h0 h1
        change t * x = A.val 0 0 * x + A.val 0 1 * 1 at h0
        change t * 1 = A.val 1 0 * x + A.val 1 1 * 1 at h1
        rw [hb, zero_mul, add_zero] at h0
        simp only [mul_one] at h1
        have hsq : A.val 1 0 * (x * x) = 0 := by
          linear_combination h0 - x * h1 + x * hd
        have hx : x = 0 := mul_self_eq_zero.mp ((mul_eq_zero.mp hsq).resolve_left hc)
        exact congrArg some hx
      · intro h
        have hx : x = 0 := Option.some.inj h
        subst x
        apply OddPSLTwoSplitInvolution.quotient_fixed_of_mulVec F A (some 0) (A.val 1 1)
        ext j
        fin_cases j <;> simp [representative, Matrix.mulVec, dotProduct,
          Fin.sum_univ_two, hb]

theorem unique_coordinate_fixed_of_odd_commute (hunits : IsPGroup 2 Fˣ)
    (s : Fˣ) (hs : (s : F) ^ 4 ≠ 1) (A : SLTwo.SL2 F)
    (hA : Odd (orderOf A)) (hne : quotient F A ≠ 1)
    (hc : Commute A (SLTwo.tor s * A * (SLTwo.tor s)⁻¹)) :
    ∃ x : Option F, (x = none ∨ x = some 0) ∧
      ∀ y : Option F, quotient F A • y = y ↔ y = x := by
  rcases diagonal_or_root_of_commute_torus_conjugate F s hs A hc with
    hdiag | hupper | hlower
  · obtain ⟨r, hr⟩ := eq_torus_of_diagonal F A hdiag.1 hdiag.2
    have hrOdd : Odd (orderOf r) := by
      rw [hr] at hA
      change Odd (orderOf (SLTwo.torHom F r)) at hA
      rw [orderOf_injective (SLTwo.torHom F) (SLTwo.torHom_injective (K := F))] at hA
      exact hA
    have hr1 := eq_one_of_binary_odd hunits r hrOdd
    exact (hne (by rw [hr, hr1, show SLTwo.tor (1 : Fˣ) = 1 from
      (SLTwo.torHom F).map_one, map_one])).elim
  · exact ⟨none, Or.inl rfl, upper_unique_fixed F A hupper.1 hupper.2.1 hupper.2.2⟩
  · exact ⟨some 0, Or.inr rfl, lower_unique_fixed F A hlower.1 hlower.2.1 hlower.2.2⟩

section FiniteField

variable [Finite F]

theorem center_isPGroup_two (hodd : Odd (Nat.card F)) :
    IsPGroup 2 (Subgroup.center (SLTwo.SL2 F)) := by
  apply IsPGroup.of_card (n := 1)
  simpa only [pow_one] using OddSLTwoCenter.card_center F hodd

/-- Every odd abelian normal subgroup of a soluble-overgroup candidate
forces that candidate into one of the two coordinate Borels. -/
theorem borel_of_odd_normal (hodd : Odd (Nat.card F)) (hunits : IsPGroup 2 Fˣ)
    (s : Fˣ) (hs : (s : F) ^ 4 ≠ 1)
    (H : Subgroup (Q F)) (hd : projectiveTorusHom F s ∈ H)
    (E : Subgroup H) [E.Normal] [IsMulCommutative E] (hne : E ≠ ⊥)
    (hEodd : ∀ e : E, Odd (orderOf e)) :
    H ≤ OddPSLTwoBorel.borel F ∨
      H ≤ MulAction.stabilizer (Q F) (some (0 : F) : Option F) := by
  obtain ⟨e, he⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  let e₀ : Q F := H.subtype (E.subtype e)
  have he₀ : e₀ ≠ 1 := by
    intro h
    apply he
    apply Subtype.ext
    apply Subtype.ext
    exact h
  have heOdd : Odd (orderOf e₀) := by
    simpa only [e₀, orderOf_injective H.subtype H.subtype_injective,
      orderOf_injective E.subtype E.subtype_injective] using hEodd e
  obtain ⟨A, hA, horder⟩ := exists_order_preserving_lift_of_pgroup Nat.prime_two
    (Subgroup.center (SLTwo.SL2 F)) (center_isPGroup_two F hodd) e₀
      (Nat.prime_two.coprime_iff_not_dvd.mp heOdd.coprime_two_left)
  change quotient F A = e₀ at hA
  have hAOdd : Odd (orderOf A) := horder.symm ▸ heOdd
  let d : H := ⟨projectiveTorusHom F s, hd⟩
  let e' : E := MulAut.conjNormal d e
  have hcomm : Commute e₀
      (projectiveTorusHom F s * e₀ * (projectiveTorusHom F s)⁻¹) := by
    exact congrArg H.subtype (congrArg E.subtype (mul_comm e e'))
  have hmapcomm : Commute (quotient F A)
      (quotient F (SLTwo.tor s * A * (SLTwo.tor s)⁻¹)) := by
    simpa only [map_mul, map_inv, hA, ← projectiveTorusHom_apply] using hcomm
  have hAcomm : Commute A (SLTwo.tor s * A * (SLTwo.tor s)⁻¹) := by
    apply commute_of_odd_map_commute (quotient F)
      (by change (QuotientGroup.mk' (Subgroup.center (SLTwo.SL2 F))).ker ≤ _; simp)
      (by
        change IsPGroup 2 (QuotientGroup.mk' (Subgroup.center (SLTwo.SL2 F))).ker
        rw [QuotientGroup.ker_mk']
        exact center_isPGroup_two F hodd)
      A _ _ hmapcomm
    simpa only [← MulAut.conj_apply, MulEquiv.orderOf_eq] using hAOdd
  obtain ⟨x, hx, hfix⟩ := unique_coordinate_fixed_of_odd_commute F hunits s hs A hAOdd
    (by rwa [hA]) hAcomm
  have hfixH : ∀ h : H, (h : Q F) • x = x := by
    apply fixed_of_normal_unique E e x
    intro y
    change e₀ • y = y ↔ y = x
    rw [← hA]
    exact hfix y
  rcases hx with rfl | rfl
  · exact Or.inl (fun g hg => hfixH ⟨g, hg⟩)
  · exact Or.inr (fun g hg => hfixH ⟨g, hg⟩)

omit [Finite F] in
theorem commute_image_of_conjugation_eq_one (H : Subgroup (Q F))
    (E : Subgroup H) [E.Normal] (g : H)
    (ha : MulAut.conjNormal g = (1 : MulAut E)) (e : E) :
    Commute (g : Q F) (H.subtype (E.subtype e)) := by
  have he : g * (e : H) * g⁻¹ = (e : H) :=
    congrArg E.subtype (congrArg (fun a : MulAut E => a e) ha)
  have he' : g * (e : H) = (e : H) * g := mul_inv_eq_iff_eq_mul.mp he
  exact congrArg H.subtype he'

/-- A normal elementary abelian binary subgroup has order two in a
soluble overgroup containing a split element whose fourth power is not one.
That order-two subgroup forces preservation of the coordinate pair. -/
theorem dihedral_of_binary_normal (hunits : IsPGroup 2 Fˣ)
    (s : Fˣ) (hd4 : (projectiveTorusHom F s) ^ 4 ≠ 1)
    (i : Fˣ) (hi : (i : F) ^ 2 = -1) (hine : (i : F) ^ 2 ≠ 1)
    (H : Subgroup (Q F)) (hd : projectiveTorusHom F s ∈ H)
    (E : Subgroup H) [E.Normal] [IsElementaryAbelian 2 E] (hne : E ≠ ⊥) :
    H ≤ subgroup F := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let E₀ : Subgroup (Q F) := E.map H.subtype
  let : IsElementaryAbelian 2 E₀ := IsElementaryAbelian.map H.subtype
  have hcard : Nat.card E₀ = Nat.card E :=
    Subgroup.card_map_of_injective H.subtype_injective
  have hbound : Nat.card E ≤ 4 := by
    rw [← hcard]
    exact OddPSLTwoSplitInvolution.card_elementary_two_le_four F E₀ i hi hine
  obtain ⟨e, he⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hlarge : 1 < Nat.card E := (Subgroup.one_lt_card_iff_ne_bot E).mpr hne
  have heven : 2 ∣ Nat.card E :=
    (IsElementaryAbelian.isPGroup 2 E).dvd_orderOf he |>.trans (orderOf_dvd_natCard e)
  have hcases : Nat.card E = 2 ∨ Nat.card E = 4 := by omega
  let d : H := ⟨projectiveTorusHom F s, hd⟩
  have hd2 : (projectiveTorusHom F s) ^ 2 ≠ 1 := by
    intro h
    apply hd4
    calc
      _ = ((projectiveTorusHom F s) ^ 2) ^ 2 := by rw [← pow_mul]
      _ = 1 := by rw [h, one_pow]
  rcases hcases with hc2 | hc4
  · let e₀ : Q F := H.subtype (E.subtype e)
    have hene : e₀ ≠ 1 := by
      intro h
      exact he (Subtype.ext (Subtype.ext h))
    have hde : Commute (projectiveTorusHom F s) e₀ :=
      commute_image_of_conjugation_eq_one F H E d
        (SmallNormalTwoAction.conjugation_eq_one_of_card_two E hc2 d) e
    have heT : e₀ ∈ (projectiveTorusHom F).range := by
      rw [← centralizer_torus_eq_range F s hd2]
      exact Subgroup.mem_centralizer_singleton_iff.mpr hde.symm
    obtain ⟨r, hr⟩ := heT
    have hrsq : (projectiveTorusHom F r) ^ 2 = 1 := by
      rw [hr]
      exact congrArg H.subtype
        (elemPow_eq_one_of_isElementaryAbelian (e : H) e.property)
    have hei : e₀ = projectiveTorusHom F i := by
      rcases (torus_sq_eq_one_iff F i r hi).mp hrsq with h1 | hi'
      · exact (hene (hr.symm.trans h1)).elim
      · exact hr.symm.trans hi'
    intro g hg
    have hge : Commute g e₀ :=
      commute_image_of_conjugation_eq_one F H E ⟨g, hg⟩
        (SmallNormalTwoAction.conjugation_eq_one_of_card_two E hc2 ⟨g, hg⟩) e
    rw [hei] at hge
    exact mem_splitDihedral_of_commute F i hine g hge
  · have hpow : ∃ n : ℕ, d ^ (2 ^ n) = 1 := by
      obtain ⟨n, hn⟩ := hunits s
      refine ⟨n, Subtype.ext ?_⟩
      change (projectiveTorusHom F s) ^ (2 ^ n) = 1
      rw [← map_pow, hn, map_one]
    have hconj := SmallNormalTwoAction.conjugation_sq_eq_one_of_card_four E hc4 d hpow
    have hdc : (projectiveTorusHom F s) ^ 2 ∈ Subgroup.centralizer (E₀ : Set (Q F)) := by
      apply Subgroup.mem_centralizer_iff.mpr
      rintro z ⟨e', he', rfl⟩
      exact (commute_image_of_conjugation_eq_one F H E (d ^ 2) hconj ⟨e', he'⟩).eq.symm
    have hc4' : Nat.card E₀ = 4 := hcard.trans hc4
    rw [OddPSLTwoSplitInvolution.centralizer_elementary_four_eq_self F E₀ hc4' i hi hine] at hdc
    have hs := elemPow_eq_one_of_isElementaryAbelian (p := 2)
      ((projectiveTorusHom F s) ^ 2) hdc
    exact (hd4 (by simpa only [← pow_mul] using hs)).elim

/-- Structural form with a concrete square root of minus one. The final
finite-field wrapper derives that square root from the unit-group order. -/
theorem soluble_overgroup_of_square_root (hodd : Odd (Nat.card F))
    (hunits : IsPGroup 2 Fˣ) (s : Fˣ)
    (hd4 : (projectiveTorusHom F s) ^ 4 ≠ 1)
    (i : Fˣ) (hi : (i : F) ^ 2 = -1) (hine : (i : F) ^ 2 ≠ 1)
    (H : Subgroup (Q F)) [Group.IsSolvable H]
    (hd : projectiveTorusHom F s ∈ H) :
    H ≤ OddPSLTwoBorel.borel F ∨
      H ≤ MulAction.stabilizer (Q F) (some (0 : F) : Option F) ∨
      H ≤ subgroup F := by
  classical
  have hs : (s : F) ^ 4 ≠ 1 := by
    intro h
    apply hd4
    have hs' : s ^ 4 = 1 := Units.ext h
    rw [← map_pow, hs', map_one]
  have hH : H ≠ ⊥ := by
    intro h
    have he : projectiveTorusHom F s = 1 := by simpa only [h, Subgroup.mem_bot] using hd
    exact hd4 (by rw [he, one_pow])
  let : Nontrivial H := (Subgroup.nontrivial_iff_ne_bot H).mpr hH
  obtain ⟨E, hEnormal, _, hEne, hEmin⟩ :=
    exists_minimal_normal_le (⊤ : Subgroup H) inferInstance top_ne_bot
  let : E.Normal := hEnormal
  let : IsMinimalNormal E :=
    { minimal := fun K hK hle => by
        by_cases hbot : K = ⊥
        · exact Or.inl hbot
        · exact Or.inr (hEmin K hK hle hbot) }
  obtain ⟨p, hp, hEA⟩ := minimalNormal_solvable_exists_isElementaryAbelian E
  let : IsElementaryAbelian p E := hEA
  by_cases hp2 : p = 2
  · subst p
    exact Or.inr (Or.inr (dihedral_of_binary_normal F hunits s hd4 i hi hine H hd E hEne))
  · have hpOdd : Odd p := hp.odd_of_ne_two hp2
    have hEodd : ∀ e : E, Odd (orderOf e) := fun e =>
      ((IsElementaryAbelian.isPGroup p E).orderOf_coprime hpOdd.coprime_two_right e).odd_of_right
    rcases borel_of_odd_normal F hodd hunits s hs H hd E hEne hEodd with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

theorem exists_sqrt_neg_one (hodd : Odd (Nat.card F)) (hunits : IsPGroup 2 Fˣ)
    (s : Fˣ) (hd4 : (projectiveTorusHom F s) ^ 4 ≠ 1) :
    ∃ i : Fˣ, (i : F) ^ 2 = -1 ∧ (i : F) ^ 2 ≠ 1 := by
  classical
  let : Fintype F := Fintype.ofFinite F
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hunits.exists_card_eq
  have hn2 : 2 ≤ n := by
    by_contra h
    have hd : Nat.card Fˣ ∣ 4 := by
      rw [hn]
      exact Nat.pow_dvd_pow 2 (by omega : n ≤ 2)
    have hs : s ^ 4 = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_natCard s).trans hd)
    exact hd4 (by rw [← map_pow, hs, map_one])
  have hd : 4 ∣ Nat.card Fˣ := by
    rw [hn]
    exact Nat.pow_dvd_pow 2 hn2
  have hsum := Nat.card_eq_card_units_add_one F
  have hmod : Fintype.card F % 4 ≠ 3 := by
    rw [← Nat.card_eq_fintype_card]
    omega
  obtain ⟨i, hi⟩ := (FiniteField.isSquare_neg_one_iff (F := F)).mpr hmod
  have hi0 : i ≠ 0 := by
    intro h
    rw [h, mul_zero] at hi
    exact neg_ne_zero.mpr one_ne_zero hi
  have hs : i ^ 2 = -1 := by simpa only [pow_two] using hi.symm
  refine ⟨Units.mk0 i hi0, hs, ?_⟩
  change i ^ 2 ≠ 1
  rw [hs]
  exact Ring.neg_one_ne_one_of_char_ne_two (OddSLTwoCenter.ringChar_ne_two F hodd)

/-- Actual soluble-overgroup classification needed for the Fermat route.
The element need not be a generator of the full torus: a fourth power
different from one suffices. The square-root premise is derived here. -/
theorem soluble_overgroup (hodd : Odd (Nat.card F)) (hunits : IsPGroup 2 Fˣ)
    (s : Fˣ) (hd4 : (projectiveTorusHom F s) ^ 4 ≠ 1)
    (H : Subgroup (Q F)) [Group.IsSolvable H]
    (hd : projectiveTorusHom F s ∈ H) :
    H ≤ OddPSLTwoBorel.borel F ∨
      H ≤ MulAction.stabilizer (Q F) (some (0 : F) : Option F) ∨
      H ≤ subgroup F := by
  obtain ⟨i, hi, hine⟩ := exists_sqrt_neg_one F hodd hunits s hd4
  exact soluble_overgroup_of_square_root F hodd hunits s hd4 i hi hine H hd

/-- Cardinal form for the actual finite-field application. No
minimal-simple classification, generation premise, or prime-field premise
is used in this structural overgroup theorem. -/
theorem soluble_overgroup_of_card_units (hodd : Odd (Nat.card F))
    (n : ℕ) (hcard : Nat.card Fˣ = 2 ^ n)
    (s : Fˣ) (horder : 8 ≤ orderOf (projectiveTorusHom F s))
    (H : Subgroup (Q F)) [Group.IsSolvable H]
    (hd : projectiveTorusHom F s ∈ H) :
    H ≤ OddPSLTwoBorel.borel F ∨
      H ≤ MulAction.stabilizer (Q F) (some (0 : F) : Option F) ∨
      H ≤ subgroup F := by
  apply soluble_overgroup F hodd (IsPGroup.of_card hcard) s _ H hd
  intro h
  have hle := Nat.le_of_dvd (by decide : 0 < 4) (orderOf_dvd_of_pow_eq_one h)
  omega

end FiniteField

end Kourovka2135.OddPSLTwoFermatOvergroup
