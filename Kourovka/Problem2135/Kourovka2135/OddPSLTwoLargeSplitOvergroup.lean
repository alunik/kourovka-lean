import Kourovka2135.OddPSLTwoElementaryTwo
import Kourovka2135.OddPSLTwoFermatOvergroup

/-! Soluble overgroups of a sufficiently large split element over any odd field.

The odd normal-subgroup case permits a diagonal subgroup as well as a root
subgroup. The binary case uses the actual rank-two bound after extension of
the field. The condition `s ^ 24 ≠ 1` excludes all possible actions on a normal
four-group through the elementary faithful permutation action on its three
nonidentity elements. There is no hypothesis that the full unit group is binary.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.OddPSLTwoLargeSplitOvergroup

open OddPSLTwoProjectiveChart OddPSLTwoTorusMovingRank
open OddPSLTwoSplitDihedral OddPSLTwoSplitCentralizer OddPSLTwoFermatOvergroup
open scoped IsMulCommutative

variable (F : Type*) [Field F]

theorem fourth_power_ne_one (s : Fˣ) (hs : (s : F) ^ 24 ≠ 1) :
    (s : F) ^ 4 ≠ 1 := by
  intro h
  apply hs
  calc
    (s : F) ^ 24 = ((s : F) ^ 4) ^ 6 := by ring
    _ = 1 := by rw [h, one_pow]

theorem projective_twelfth_power_ne_one (s : Fˣ) (hs : (s : F) ^ 24 ≠ 1) :
    (projectiveTorusHom F s) ^ 12 ≠ 1 := by
  intro h
  have he : projectiveTorusHom F (s ^ 12) = 1 := by rwa [map_pow]
  have he' := (torus_eq_one_iff F (s ^ 12)).mp he
  apply hs
  simpa only [Units.val_pow_eq_pow_val, ← pow_mul] using he'

theorem projective_square_ne_one (s : Fˣ) (hs : (s : F) ^ 24 ≠ 1) :
    (projectiveTorusHom F s) ^ 2 ≠ 1 := by
  intro h
  apply projective_twelfth_power_ne_one F s hs
  calc
    _ = ((projectiveTorusHom F s) ^ 2) ^ 6 := by rw [← pow_mul]
    _ = 1 := by rw [h, one_pow]

/-- A normal diagonal subgroup containing a nonidentity non-involution
forces preservation of the coordinate pair. -/
theorem pair_of_normal_torus (H : Subgroup (Q F)) (E : Subgroup H) [E.Normal]
    (hET : ∀ z : E, (z : Q F) ∈ (projectiveTorusHom F).range)
    (e : E) (r : Fˣ) (her : (e : Q F) = projectiveTorusHom F r)
    (hr : (r : F) ^ 2 ≠ 1) : H ≤ subgroup F := by
  have hEfix (z : E) (x : Option F) (hx : x = none ∨ x = some 0) :
      (z : Q F) • x = x := by
    obtain ⟨t, ht⟩ := hET z
    rw [← ht]
    rcases hx with rfl | rfl
    · exact tor_smul_none F t
    · simp only [projectiveTorusHom_apply, tor_smul_some, mul_zero]
  intro g hg
  let g' : H := ⟨g, hg⟩
  let z : E := MulAut.conjNormal g'⁻¹ e
  have hfixed (x : Option F) (hx : x = none ∨ x = some 0) :
      projectiveTorusHom F r • (g • x) = g • x := by
    rw [← her]
    calc
      (e : Q F) • (g • x) = g • ((z : Q F) • x) := by
        simp only [← mul_smul]
        congr 1
        dsimp [z]
        simp only [inv_inv]
        change (e : Q F) * g = g * (g⁻¹ * (e : Q F) * g)
        group
      _ = g • x := congrArg (fun y => g • y) (hEfix z x hx)
  have hn := (torus_fixed_iff F r hr (g • none)).mp (hfixed none (Or.inl rfl))
  have hz := (torus_fixed_iff F r hr (g • some 0)).mp (hfixed (some 0) (Or.inr rfl))
  apply (mem_subgroup_iff F g).mpr
  rcases hn with hn | hn <;> rcases hz with hz | hz
  · have he : (none : Option F) = some 0 := MulAction.injective g (hn.trans hz.symm)
    cases he
  · exact Or.inl ⟨hn, hz⟩
  · exact Or.inr ⟨hn, hz⟩
  · have he : (none : Option F) = some 0 := MulAction.injective g (hn.trans hz.symm)
    cases he

variable [Finite F]

/-- An odd abelian normal subgroup yields a Borel or the split-pair stabilizer. -/
theorem borel_or_dihedral_of_odd_normal (hodd : Odd (Nat.card F))
    (s : Fˣ) (hs : (s : F) ^ 4 ≠ 1)
    (H : Subgroup (Q F)) (hd : projectiveTorusHom F s ∈ H)
    (E : Subgroup H) [E.Normal] [IsMulCommutative E] (hne : E ≠ ⊥)
    (hEodd : ∀ e : E, Odd (orderOf e)) :
    H ≤ OddPSLTwoBorel.borel F ∨
      H ≤ MulAction.stabilizer (Q F) (some (0 : F) : Option F) ∨
      H ≤ subgroup F := by
  obtain ⟨e, he⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  let e₀ : Q F := H.subtype (E.subtype e)
  have he₀ : e₀ ≠ 1 := by
    intro h
    exact he (Subtype.ext (Subtype.ext h))
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
  rcases diagonal_or_root_of_commute_torus_conjugate F s hs A hAcomm with
    hdiag | hupper | hlower
  · obtain ⟨r, hr⟩ := eq_torus_of_diagonal F A hdiag.1 hdiag.2
    have her : e₀ = projectiveTorusHom F r := by rw [← hA, hr]; rfl
    have hr2 : (projectiveTorusHom F r) ^ 2 ≠ 1 := by
      rw [← her]
      intro h
      apply he₀
      apply orderOf_eq_one_iff.mp
      exact Nat.eq_one_of_dvd_coprimes heOdd.coprime_two_right dvd_rfl
        (orderOf_dvd_of_pow_eq_one h)
    have hET : ∀ z : E, (z : Q F) ∈ (projectiveTorusHom F).range := by
      intro z
      rw [← centralizer_torus_eq_range F r hr2]
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      have hc : Commute (z : Q F) e₀ :=
        congrArg H.subtype (congrArg E.subtype (mul_comm z e))
      rwa [her] at hc
    have hrne : (r : F) ^ 2 ≠ 1 := by
      intro h
      exact he₀ (her.trans ((torus_eq_one_iff F r).mpr h))
    exact Or.inr (Or.inr (pair_of_normal_torus F H E hET e r her hrne))
  · have hfixH : ∀ h : H, (h : Q F) • (none : Option F) = none := by
      apply fixed_of_normal_unique (X := Option F) E e (none : Option F)
      intro y
      change e₀ • y = y ↔ y = none
      rw [← hA]
      exact upper_unique_fixed F A hupper.1 hupper.2.1 hupper.2.2 y
    exact Or.inl (fun g hg => hfixH ⟨g, hg⟩)
  · have hfixH : ∀ h : H, (h : Q F) • (some (0 : F) : Option F) = some 0 := by
      apply fixed_of_normal_unique (X := Option F) E e (some (0 : F))
      intro y
      change e₀ • y = y ↔ y = some 0
      rw [← hA]
      exact lower_unique_fixed F A hlower.1 hlower.2.1 hlower.2.2 y
    exact Or.inr (Or.inl (fun g hg => hfixH ⟨g, hg⟩))

theorem dihedral_of_binary_normal (hodd : Odd (Nat.card F))
    (s : Fˣ) (hs : (s : F) ^ 24 ≠ 1)
    (H : Subgroup (Q F)) (hd : projectiveTorusHom F s ∈ H)
    (E : Subgroup H) [E.Normal] [IsElementaryAbelian 2 E] (hne : E ≠ ⊥) :
    H ≤ subgroup F := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hneg : (-1 : F) ≠ 1 :=
    Ring.neg_one_ne_one_of_char_ne_two (OddSLTwoCenter.ringChar_ne_two F hodd)
  let E₀ : Subgroup (Q F) := E.map H.subtype
  let : IsElementaryAbelian 2 E₀ := IsElementaryAbelian.map H.subtype
  have hcard : Nat.card E₀ = Nat.card E :=
    Subgroup.card_map_of_injective H.subtype_injective
  have hbound : Nat.card E ≤ 4 := by
    rw [← hcard]
    exact OddPSLTwoElementaryTwo.card_le_four hneg E₀
  obtain ⟨e, he⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hlarge : 1 < Nat.card E := (Subgroup.one_lt_card_iff_ne_bot E).mpr hne
  have heven : 2 ∣ Nat.card E :=
    (IsElementaryAbelian.isPGroup 2 E).dvd_orderOf he |>.trans (orderOf_dvd_natCard e)
  have hcases : Nat.card E = 2 ∨ Nat.card E = 4 := by omega
  let d : H := ⟨projectiveTorusHom F s, hd⟩
  rcases hcases with hc2 | hc4
  · let e₀ : Q F := H.subtype (E.subtype e)
    have hene : e₀ ≠ 1 := fun h => he (Subtype.ext (Subtype.ext h))
    have hde : Commute (projectiveTorusHom F s) e₀ :=
      commute_image_of_conjugation_eq_one F H E d
        (SmallNormalTwoAction.conjugation_eq_one_of_card_two E hc2 d) e
    have heT : e₀ ∈ (projectiveTorusHom F).range := by
      rw [← centralizer_torus_eq_range F s (projective_square_ne_one F s hs)]
      exact Subgroup.mem_centralizer_singleton_iff.mpr hde.symm
    obtain ⟨r, hr⟩ := heT
    have hrne : (r : F) ^ 2 ≠ 1 := by
      intro h
      exact hene (hr.symm.trans ((torus_eq_one_iff F r).mpr h))
    intro g hg
    have hge : Commute g e₀ :=
      commute_image_of_conjugation_eq_one F H E ⟨g, hg⟩
        (SmallNormalTwoAction.conjugation_eq_one_of_card_two E hc2 ⟨g, hg⟩) e
    rw [← hr] at hge
    exact mem_splitDihedral_of_commute F r hrne g hge
  · have hd6 : MulAut.conjNormal (d ^ 6) = (1 : MulAut E) := by
      rw [map_pow]
      apply orderOf_dvd_iff_pow_eq_one.mp
      have hh := SmallNormalTwoAction.orderOf_dvd_factorial (MulAut.conjNormal d : MulAut E)
      simpa only [hc4, Nat.reduceSub, Nat.factorial] using hh
    have hdc : (projectiveTorusHom F s) ^ 6 ∈ Subgroup.centralizer (E₀ : Set (Q F)) := by
      apply Subgroup.mem_centralizer_iff.mpr
      rintro z ⟨e', he', rfl⟩
      exact (commute_image_of_conjugation_eq_one F H E (d ^ 6) hd6 ⟨e', he'⟩).eq.symm
    rw [OddPSLTwoElementaryTwo.centralizer_eq_self hneg E₀ (hcard.trans hc4)] at hdc
    have hp := elemPow_eq_one_of_isElementaryAbelian (p := 2)
      ((projectiveTorusHom F s) ^ 6) hdc
    exact (projective_twelfth_power_ne_one F s hs
      (by simpa only [← pow_mul] using hp)).elim

/-- Uniform elementary soluble-overgroup alternative. -/
theorem soluble_overgroup (hodd : Odd (Nat.card F))
    (s : Fˣ) (hs : (s : F) ^ 24 ≠ 1)
    (H : Subgroup (Q F)) [Group.IsSolvable H]
    (hd : projectiveTorusHom F s ∈ H) :
    H ≤ OddPSLTwoBorel.borel F ∨
      H ≤ MulAction.stabilizer (Q F) (some (0 : F) : Option F) ∨
      H ≤ subgroup F := by
  classical
  have hH : H ≠ ⊥ := by
    intro h
    have he : projectiveTorusHom F s = 1 := by simpa only [h, Subgroup.mem_bot] using hd
    exact projective_twelfth_power_ne_one F s hs (by rw [he, one_pow])
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
    exact Or.inr (Or.inr (dihedral_of_binary_normal F hodd s hs H hd E hEne))
  · have hpOdd : Odd p := hp.odd_of_ne_two hp2
    have hEodd : ∀ e : E, Odd (orderOf e) := fun e =>
      ((IsElementaryAbelian.isPGroup p E).orderOf_coprime hpOdd.coprime_two_right e).odd_of_right
    exact borel_or_dihedral_of_odd_normal F hodd s (fourth_power_ne_one F s hs)
      H hd E hEne hEodd

end Kourovka2135.OddPSLTwoLargeSplitOvergroup
