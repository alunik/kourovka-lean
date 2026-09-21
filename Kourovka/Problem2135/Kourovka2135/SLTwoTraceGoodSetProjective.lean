import Kourovka2135.SLTwoTraceGoodSet
import Kourovka2135.OddPSLTwoSplitInvolution
import Kourovka2135.CentralReferenceGoodSet

/-! The broad trace good set has a genuine odd element and its actual
projective image avoids the identity and all involutions. -/

set_option autoImplicit false
noncomputable section
namespace Kourovka2135.SLTwoTraceGoodSetProjective
open scoped Matrix
open SLTwoTraceGoodSet SLTwoNonscalarWordValues OddPSLTwoProjectiveChart
variable {F : Type*} [Field F]

def projectiveGoodSet : Set (Q F) := quotient F '' (goodSet (F := F))

theorem not_mem_center_of_nonscalar (g : SLTwo.SL2 F) (hg : Nonscalar g) :
    g ∉ Subgroup.center (SLTwo.SL2 F) := by
  intro hc
  obtain ⟨r, _, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hc
  exact hg ⟨r, hr.symm⟩

theorem quotient_ne_one (g : SLTwo.SL2 F) (hg : Nonscalar g) : quotient F g ≠ 1 := by
  intro he
  exact not_mem_center_of_nonscalar g hg ((QuotientGroup.eq_one_iff _).mp he)

theorem one_not_mem : (1 : Q F) ∉ projectiveGoodSet := by
  rintro ⟨g, hg, he⟩
  exact quotient_ne_one g hg.1 he

theorem square_ne_one {g : Q F} (hg : g ∈ projectiveGoodSet) : g ^ 2 ≠ 1 := by
  obtain ⟨A, hA, rfl⟩ := hg
  intro he
  have hc : A ^ 2 ∈ Subgroup.center (SLTwo.SL2 F) := by
    apply (QuotientGroup.eq_one_iff _).mp
    change quotient F (A ^ 2) = 1
    rwa [map_pow]
  have hz := OddPSLTwoSplitInvolution.trace_zero_of_square_central F A hc
    (not_mem_center_of_nonscalar A hA.1)
  exact hA.2.2 (by simpa only [Matrix.trace_fin_two] using hz)

def cycleThree : SLTwo.SL2 F := ⟨!![0, -1; 1, -1], by simp [Matrix.det_fin_two_of]⟩

theorem cycleThree_cube : (cycleThree (F := F)) ^ 3 = 1 := by
  apply Subtype.ext
  change (cycleThree (F := F)).val ^ 3 = (1 : Matrix (Fin 2) (Fin 2) F)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cycleThree, pow_succ, Matrix.mul_apply, Fin.sum_univ_two]

theorem cycleThree_odd : Odd (orderOf (cycleThree (F := F))) :=
  (by decide : Odd (3 : ℕ)).of_dvd_nat (orderOf_dvd_of_pow_eq_one cycleThree_cube)

theorem cycleThree_mem (h3 : (3 : F) ≠ 0) : cycleThree (F := F) ∈ goodSet := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨r, hr⟩
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 1 0) hr
    simp [cycleThree] at h
  · rw [Matrix.trace_fin_two]
    change (0 : F) + -1 ≠ 2
    intro he
    apply h3
    linear_combination -he
  · rw [Matrix.trace_fin_two]
    change (0 : F) + -1 ≠ 0
    simp

theorem tor_mem (s : Fˣ) (hs4 : (s : F) ^ 4 ≠ 1) : SLTwo.tor s ∈ goodSet := by
  have hs2 : (s : F) ^ 2 ≠ 1 := by
    intro he
    apply hs4
    calc (s : F) ^ 4 = ((s : F) ^ 2) ^ 2 := by ring
         _ = 1 := by rw [he]; simp
  refine ⟨tor_nonscalar s hs2, ?_, ?_⟩
  · rw [Matrix.trace_fin_two]
    simp only [SLTwo.tor, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Units.val_inv_eq_inv_val]
    intro he
    have hi := mul_inv_cancel₀ s.ne_zero
    have hz : ((s : F) - 1) ^ 2 = 0 := by linear_combination (s : F) * he - hi
    have hone := sub_eq_zero.mp (eq_zero_of_pow_eq_zero hz)
    exact hs2 (by rw [hone]; simp)
  · rw [Matrix.trace_fin_two]
    simp only [SLTwo.tor, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Units.val_inv_eq_inv_val]
    intro he
    have hi := mul_inv_cancel₀ s.ne_zero
    have hsq : (s : F) ^ 2 = -1 := by linear_combination (s : F) * he - hi
    apply hs4
    calc (s : F) ^ 4 = ((s : F) ^ 2) ^ 2 := by ring
         _ = 1 := by rw [hsq]; ring

theorem hasOddGeneratingGoodSetOver (h3 : (3 : F) ≠ 0)
    (hgood : IsGeneratingGoodSet (goodSet (F := F))) :
    HasOddGeneratingGoodSetOver (quotient F) (projectiveGoodSet (F := F)) := by
  refine ⟨goodSet, hgood, ?_, cycleThree, cycleThree_mem h3, cycleThree_odd⟩
  intro g hg
  exact ⟨g, hg, rfl⟩

end Kourovka2135.SLTwoTraceGoodSetProjective
