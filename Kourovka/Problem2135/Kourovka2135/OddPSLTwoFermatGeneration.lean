import Kourovka2135.OddPSLTwoFermatOvergroup
import Kourovka2135.SLTwoNonscalarWordValues

/-! Concrete generation over a finite field with binary unit group.

A full diagonal torus and a matrix with both off-diagonal entries nonzero
and at least one diagonal entry nonzero generate actual SL2, provided all
proper subgroups of its actual projective quotient are soluble. The
projective criterion is supplied by the elementary overgroup calculation;
the full scalar center already lies in the cyclic diagonal subgroup.

Strict compilation and ownership-audit evidence are recorded separately.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.OddPSLTwoFermatGeneration

open OddPSLTwoProjectiveChart OddPSLTwoTorusMovingRank
open OddPSLTwoSplitDihedral OddPSLTwoFermatOvergroup
open scoped Matrix LinearAlgebra.Projectivization

variable (F : Type*) [Field F]

theorem upperRight_eq_zero_of_fixed_zero (A : SLTwo.SL2 F)
    (h : quotient F A • (some (0 : F) : Option F) = some 0) : A.val 0 1 = 0 := by
  have he := congrArg (point F) h
  rw [point_smul] at he
  obtain ⟨t, ht⟩ := (Projectivization.mk_eq_mk_iff' F _ _ _ _).mp he
  change t • representative F (some 0) = A.val.mulVec (representative F (some 0)) at ht
  simpa [representative, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using
    (congrFun ht 0).symm

theorem upperLeft_eq_zero_of_swap (A : SLTwo.SL2 F)
    (h : quotient F A • (none : Option F) = some 0) : A.val 0 0 = 0 := by
  have he := congrArg (point F) h
  rw [point_smul] at he
  obtain ⟨t, ht⟩ := (Projectivization.mk_eq_mk_iff' F _ _ _ _).mp he
  change t • representative F (some 0) = A.val.mulVec (representative F none) at ht
  simpa [representative, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using
    (congrFun ht 0).symm

theorem lowerRight_eq_zero_of_swap (A : SLTwo.SL2 F)
    (h : quotient F A • (some (0 : F) : Option F) = none) : A.val 1 1 = 0 := by
  have he := congrArg (point F) h
  rw [point_smul] at he
  obtain ⟨t, ht⟩ := (Projectivization.mk_eq_mk_iff' F _ _ _ _).mp he
  change t • representative F none = A.val.mulVec (representative F (some 0)) at ht
  simpa [representative, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using
    (congrFun ht 1).symm

theorem not_mem_dihedral (A : SLTwo.SL2 F)
    (hc : A.val 1 0 ≠ 0) (hdiag : A.val 0 0 ≠ 0 ∨ A.val 1 1 ≠ 0) :
    quotient F A ∉ subgroup F := by
  intro h
  rcases (mem_subgroup_iff F _).mp h with hfix | hswap
  · exact hc (OddPSLTwoBorel.lowerLeft_eq_zero F A hfix.1)
  · rcases hdiag with h | h
    · exact h (upperLeft_eq_zero_of_swap F A hswap.1)
    · exact h (lowerRight_eq_zero_of_swap F A hswap.2)

variable [Finite F]

theorem zpowers_eq_top_of_full_order (s : Fˣ) (hs : orderOf s = Nat.card Fˣ) :
    Subgroup.zpowers s = ⊤ :=
  Subgroup.eq_top_of_card_eq (Subgroup.zpowers s)
    (by simpa only [Nat.card_zpowers] using hs)

theorem center_le_zpowers_torus (s : Fˣ) (hs : orderOf s = Nat.card Fˣ) :
    Subgroup.center (SLTwo.SL2 F) ≤ Subgroup.zpowers (SLTwo.tor s) := by
  intro A hA
  obtain ⟨r, _, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  have hb : A.val 0 1 = 0 := by
    simpa [Matrix.scalar] using
      (congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 0 1) hr).symm
  have hc : A.val 1 0 = 0 := by
    simpa [Matrix.scalar] using
      (congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 1 0) hr).symm
  obtain ⟨t, rfl⟩ := eq_torus_of_diagonal F A hb hc
  have ht : t ∈ Subgroup.zpowers s := by rw [zpowers_eq_top_of_full_order F s hs]; trivial
  obtain ⟨m, hm⟩ := ht
  change s ^ m = t at hm
  refine ⟨m, ?_⟩
  change (SLTwo.torHom F s) ^ m = SLTwo.torHom F t
  rw [← map_zpow, hm]

/-- In particular the genuine negative identity is an actual power of
the diagonal generator; the central kernel is not lost on lifting. -/
theorem exists_zpow_minusOne (s : Fˣ) (hs : orderOf s = Nat.card Fˣ) :
    ∃ m : ℤ, (SLTwo.tor s) ^ m = OddSLTwoCenter.minusOne F :=
  center_le_zpowers_torus F s hs (OddSLTwoCenter.minusOne_mem_center F)

theorem projective_order_ge_eight (hodd : Odd (Nat.card F)) (s : Fˣ)
    (hs : orderOf s = Nat.card Fˣ) (hlarge : 16 ≤ Nat.card Fˣ) :
    8 ≤ orderOf (projectiveTorusHom F s) := by
  have hd := orderOf_dvd_orderOf_quotient_mul_card
    (Subgroup.center (SLTwo.SL2 F)) (SLTwo.tor s)
  change orderOf (SLTwo.torHom F s) ∣
    orderOf (projectiveTorusHom F s) * Nat.card (Subgroup.center (SLTwo.SL2 F)) at hd
  rw [orderOf_injective (SLTwo.torHom F) (SLTwo.torHom_injective (K := F)),
    hs, OddSLTwoCenter.card_center F hodd] at hd
  have hl := Nat.le_of_dvd (mul_pos (orderOf_pos _) (by decide : 0 < 2)) hd
  omega

omit [Finite F] in
theorem fourth_power_ne_one (s : Fˣ) (hs : orderOf s = Nat.card Fˣ)
    (hlarge : 16 ≤ Nat.card Fˣ) : (s : F) ^ 4 ≠ 1 := by
  intro h
  have hu : s ^ 4 = 1 := Units.ext h
  have hd := Nat.le_of_dvd (by decide : 0 < 4) (orderOf_dvd_of_pow_eq_one hu)
  rw [hs] at hd
  omega

theorem nonsquare_of_full_order (hodd : Odd (Nat.card F)) (s : Fˣ)
    (hs : orderOf s = Nat.card Fˣ) (hlarge : 16 ≤ Nat.card Fˣ) :
    ¬ IsSquare (s : F) := by
  rintro ⟨t, ht⟩
  have ht0 : t ≠ 0 := by
    intro h
    rw [h, mul_zero] at ht
    exact s.ne_zero ht
  let u : Fˣ := Units.mk0 t ht0
  have hsu : s = u ^ 2 := Units.ext (by
    change (s : F) = t ^ 2
    simpa only [pow_two] using ht)
  have hsum := Nat.card_eq_card_units_add_one F
  obtain ⟨k, hk⟩ := hodd
  have heven : 2 ∣ Nat.card Fˣ := by omega
  have htwice : 2 * (Nat.card Fˣ / 2) = Nat.card Fˣ := by omega
  have hpow : s ^ (Nat.card Fˣ / 2) = 1 := by
    rw [hsu, ← pow_mul, htwice]
    exact pow_card_eq_one'
  have hd := orderOf_dvd_of_pow_eq_one hpow
  rw [hs] at hd
  have hl := Nat.le_of_dvd (by omega : 0 < Nat.card Fˣ / 2) hd
  omega

theorem exists_primitive (hodd : Odd (Nat.card F)) (hlarge : 16 ≤ Nat.card Fˣ) :
    ∃ s : Fˣ, orderOf s = Nat.card Fˣ ∧ ¬ IsSquare (s : F) ∧
      (s : F) ^ 4 ≠ 1 ∧ 8 ≤ orderOf (projectiveTorusHom F s) := by
  obtain ⟨s, hs⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp
    (inferInstance : IsCyclic Fˣ)
  exact ⟨s, hs, nonsquare_of_full_order F hodd s hs hlarge,
    fourth_power_ne_one F s hs hlarge, projective_order_ge_eight F hodd s hs hlarge⟩

theorem projective_generate (hodd : Odd (Nat.card F)) (n : ℕ)
    (hcard : Nat.card Fˣ = 2 ^ n) (s : Fˣ)
    (horder : 8 ≤ orderOf (projectiveTorusHom F s))
    (hsolv : ∀ H : Subgroup (Q F), H < ⊤ → Group.IsSolvable H)
    (A : SLTwo.SL2 F) (hb : A.val 0 1 ≠ 0) (hc : A.val 1 0 ≠ 0)
    (hdiag : A.val 0 0 ≠ 0 ∨ A.val 1 1 ≠ 0) :
    Subgroup.closure ({projectiveTorusHom F s, quotient F A} : Set (Q F)) = ⊤ := by
  classical
  let H : Subgroup (Q F) :=
    Subgroup.closure ({projectiveTorusHom F s, quotient F A} : Set (Q F))
  by_contra h
  have hlt : H < ⊤ := lt_top_iff_ne_top.mpr h
  let : Group.IsSolvable H := hsolv H hlt
  have hd : projectiveTorusHom F s ∈ H := Subgroup.subset_closure (by simp)
  have hA : quotient F A ∈ H := Subgroup.subset_closure (by simp)
  rcases soluble_overgroup_of_card_units F hodd n hcard s horder H hd with
    hB | hB | hD
  · exact hc (OddPSLTwoBorel.lowerLeft_eq_zero F A (hB hA))
  · exact hb (upperRight_eq_zero_of_fixed_zero F A (hB hA))
  · exact not_mem_dihedral F A hc hdiag (hD hA)

/-- The concrete diagonal/matrix criterion in the actual SL2 cover. -/
theorem generate (hodd : Odd (Nat.card F)) (n : ℕ)
    (hcard : Nat.card Fˣ = 2 ^ n) (hlarge : 16 ≤ Nat.card Fˣ)
    (s : Fˣ) (hs : orderOf s = Nat.card Fˣ)
    (hsolv : ∀ H : Subgroup (Q F), H < ⊤ → Group.IsSolvable H)
    (A : SLTwo.SL2 F) (hb : A.val 0 1 ≠ 0) (hc : A.val 1 0 ≠ 0)
    (hdiag : A.val 0 0 ≠ 0 ∨ A.val 1 1 ≠ 0) :
    Subgroup.closure ({SLTwo.tor s, A} : Set (SLTwo.SL2 F)) = ⊤ := by
  let L : Subgroup (SLTwo.SL2 F) := Subgroup.closure ({SLTwo.tor s, A} : Set (SLTwo.SL2 F))
  have hL : L.map (quotient F) = ⊤ := by
    change (Subgroup.closure ({SLTwo.tor s, A} : Set (SLTwo.SL2 F))).map (quotient F) = ⊤
    rw [MonoidHom.map_closure, Set.image_pair]
    exact projective_generate F hodd n hcard s
      (projective_order_ge_eight F hodd s hs hlarge) hsolv A hb hc hdiag
  have hker : (quotient F).ker ≤ L := by
    change (QuotientGroup.mk' (Subgroup.center (SLTwo.SL2 F))).ker ≤ L
    rw [QuotientGroup.ker_mk']
    exact (center_le_zpowers_torus F s hs).trans
      (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)))
  have he := congrArg (Subgroup.comap (quotient F)) hL
  rw [Subgroup.comap_map_eq_self hker, Subgroup.comap_top] at he
  exact he

theorem shear_generates (hodd : Odd (Nat.card F)) (n : ℕ)
    (hcard : Nat.card Fˣ = 2 ^ n) (hlarge : 16 ≤ Nat.card Fˣ)
    (s : Fˣ) (hs : orderOf s = Nat.card Fˣ)
    (hsolv : ∀ H : Subgroup (Q F), H < ⊤ → Group.IsSolvable H)
    (t : F) (ht : t ≠ 0) :
    Subgroup.closure ({SLTwo.tor s, SLTwoNonscalarWordValues.shear t} : Set (SLTwo.SL2 F)) = ⊤ :=
  generate F hodd n hcard hlarge s hs hsolv _ ht one_ne_zero (Or.inl one_ne_zero)

/-- The complete parameter package consumed by the trace and equal-trace
pair constructions. This is valid over every such finite field; the later
prime-field word argument may impose primality separately. -/
theorem exists_generating_parameter (hodd : Odd (Nat.card F)) (n : ℕ)
    (hcard : Nat.card Fˣ = 2 ^ n) (hlarge : 17 ≤ Nat.card F)
    (hsolv : ∀ H : Subgroup (Q F), H < ⊤ → Group.IsSolvable H) :
    ∃ s : Fˣ, (s : F) ^ 4 ≠ 1 ∧ (s : F) + 1 ≠ 0 ∧ ¬ IsSquare (s : F) ∧
      ∀ A : SLTwo.SL2 F, A.val 0 1 ≠ 0 → A.val 1 0 ≠ 0 →
        (A.val 0 0 ≠ 0 ∨ A.val 1 1 ≠ 0) →
        Subgroup.closure ({SLTwo.tor s, A} : Set (SLTwo.SL2 F)) = ⊤ := by
  have hlu : 16 ≤ Nat.card Fˣ := by rw [Nat.card_units]; omega
  obtain ⟨s, hs, hns, hs4, _⟩ := exists_primitive F hodd hlu
  have hs1 : (s : F) + 1 ≠ 0 := by
    intro h
    have he : (s : F) = -1 := eq_neg_of_add_eq_zero_left h
    exact hs4 (by rw [he]; ring)
  exact ⟨s, hs4, hs1, hns, generate F hodd n hcard hlu s hs hsolv⟩

end Kourovka2135.OddPSLTwoFermatGeneration
