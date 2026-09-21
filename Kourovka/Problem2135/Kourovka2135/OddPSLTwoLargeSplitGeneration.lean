import Kourovka2135.OddPSLTwoLargeSplitOvergroup
import Kourovka2135.OddPSLTwoFermatGeneration
import Kourovka2135.SLTwoTraceGoodSetProjective
import Kourovka2135.GoodSetImage

/-! Uniform broad trace generating good sets over odd fields.

The sole structural input is solubility of proper subgroups of the actual PSL2.
The explicit numerical condition is that the unit-group cardinal does not divide
24. It holds for every field of size at least 27 and for every prime size at least
17, and does not impose a Fermat or prime-field hypothesis on the main theorem.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.OddPSLTwoLargeSplitGeneration

open OddPSLTwoProjectiveChart OddPSLTwoTorusMovingRank
open OddPSLTwoSplitDihedral OddPSLTwoFermatGeneration

variable (F : Type*) [Field F] [Finite F]

theorem projective_generate (hodd : Odd (Nat.card F)) (s : Fˣ)
    (hs : (s : F) ^ 24 ≠ 1)
    (hsolv : ∀ H : Subgroup (Q F), H < ⊤ → Group.IsSolvable H)
    (A : SLTwo.SL2 F) (hb : A.val 0 1 ≠ 0) (hc : A.val 1 0 ≠ 0)
    (hdiag : A.val 0 0 ≠ 0 ∨ A.val 1 1 ≠ 0) :
    Subgroup.closure ({projectiveTorusHom F s, quotient F A} : Set (Q F)) = ⊤ := by
  classical
  let H : Subgroup (Q F) :=
    Subgroup.closure ({projectiveTorusHom F s, quotient F A} : Set (Q F))
  by_contra h
  let : Group.IsSolvable H := hsolv H (lt_top_iff_ne_top.mpr h)
  have hd : projectiveTorusHom F s ∈ H := Subgroup.subset_closure (by simp)
  have hA : quotient F A ∈ H := Subgroup.subset_closure (by simp)
  rcases OddPSLTwoLargeSplitOvergroup.soluble_overgroup F hodd s hs H hd with
    hB | hB | hD
  · exact hc (OddPSLTwoBorel.lowerLeft_eq_zero F A (hB hA))
  · exact hb (upperRight_eq_zero_of_fixed_zero F A (hB hA))
  · exact not_mem_dihedral F A hc hdiag (hD hA)

theorem generate (hodd : Odd (Nat.card F)) (s : Fˣ)
    (horder : orderOf s = Nat.card Fˣ) (hs : (s : F) ^ 24 ≠ 1)
    (hsolv : ∀ H : Subgroup (Q F), H < ⊤ → Group.IsSolvable H)
    (A : SLTwo.SL2 F) (hb : A.val 0 1 ≠ 0) (hc : A.val 1 0 ≠ 0)
    (hdiag : A.val 0 0 ≠ 0 ∨ A.val 1 1 ≠ 0) :
    Subgroup.closure ({SLTwo.tor s, A} : Set (SLTwo.SL2 F)) = ⊤ := by
  let L : Subgroup (SLTwo.SL2 F) := Subgroup.closure ({SLTwo.tor s, A} : Set (SLTwo.SL2 F))
  have hL : L.map (quotient F) = ⊤ := by
    change (Subgroup.closure ({SLTwo.tor s, A} : Set (SLTwo.SL2 F))).map (quotient F) = ⊤
    rw [MonoidHom.map_closure, Set.image_pair]
    exact projective_generate F hodd s hs hsolv A hb hc hdiag
  have hker : (quotient F).ker ≤ L := by
    change (QuotientGroup.mk' (Subgroup.center (SLTwo.SL2 F))).ker ≤ L
    rw [QuotientGroup.ker_mk']
    exact (center_le_zpowers_torus F s horder).trans
      (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)))
  have he := congrArg (Subgroup.comap (quotient F)) hL
  rw [Subgroup.comap_map_eq_self hker, Subgroup.comap_top] at he
  exact he

theorem exists_primitive (hcard : ¬ Nat.card Fˣ ∣ 24) :
    ∃ s : Fˣ, orderOf s = Nat.card Fˣ ∧ (s : F) ^ 24 ≠ 1 := by
  obtain ⟨s, hs⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp
    (inferInstance : IsCyclic Fˣ)
  refine ⟨s, hs, ?_⟩
  intro h
  apply hcard
  rw [← hs]
  exact orderOf_dvd_of_pow_eq_one (show s ^ 24 = 1 from Units.ext h)

theorem isGeneratingGoodSet (hodd : Odd (Nat.card F))
    (hcard : ¬ Nat.card Fˣ ∣ 24)
    (hsolv : ∀ H : Subgroup (Q F), H < ⊤ → Group.IsSolvable H) :
    IsGeneratingGoodSet (SLTwoTraceGoodSet.goodSet (F := F)) := by
  obtain ⟨s, horder, hs⟩ := exists_primitive F hcard
  have hs4 := OddPSLTwoLargeSplitOvergroup.fourth_power_ne_one F s hs
  have hs2 : (s : F) ^ 2 ≠ 1 := by
    intro h
    exact hs4 (by rw [show (s : F) ^ 4 = ((s : F) ^ 2) ^ 2 by ring, h, one_pow])
  apply SLTwoTraceGoodSet.isGeneratingGoodSet_of_shear_generation s hs2
    (Ring.two_ne_zero (OddSLTwoCenter.ringChar_ne_two F hodd))
    (SLTwoTraceGoodSetProjective.tor_mem s hs4)
  intro t ht
  exact generate F hodd s horder hs hsolv
    (SLTwoNonscalarWordValues.shear t) ht one_ne_zero (Or.inl one_ne_zero)

theorem projective_isGeneratingGoodSet (hodd : Odd (Nat.card F))
    (hcard : ¬ Nat.card Fˣ ∣ 24)
    (hsolv : ∀ H : Subgroup (Q F), H < ⊤ → Group.IsSolvable H) :
    IsGeneratingGoodSet (SLTwoTraceGoodSetProjective.projectiveGoodSet (F := F)) := by
  exact (isGeneratingGoodSet F hodd hcard hsolv).image_of_surjective
    (quotient F) (QuotientGroup.mk'_surjective _)

omit [Finite F] in
theorem card_units_not_dvd_twentyFour_of_ge (hcard : 27 ≤ Nat.card F) :
    ¬ Nat.card Fˣ ∣ 24 := by
  intro h
  have hl := Nat.le_of_dvd (by decide : 0 < 24) h
  rw [Nat.card_units] at hl
  omega

omit [Finite F] in
theorem card_units_not_dvd_twentyFour_of_prime
    (hp : (Nat.card F).Prime) (hcard : 17 ≤ Nat.card F) :
    ¬ Nat.card Fˣ ∣ 24 := by
  intro h
  rw [Nat.card_units] at h
  have hl := Nat.le_of_dvd (by decide : 0 < 24) h
  have hu : Nat.card F ≤ 25 := by omega
  interval_cases hq : Nat.card F <;> norm_num at *

end Kourovka2135.OddPSLTwoLargeSplitGeneration
