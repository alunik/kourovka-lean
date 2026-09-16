import Kourovka.Problems.P21_38.Proof.BinaryBranches
import Kourovka.External.GroupApproximation.GroupTheory.HigmanThompson.GridAffine
import Mathlib.Algebra.Order.GroupWithZero.Basic

/-!
# Binary charts of dyadic coordinates

Finite dyadic grid coordinates in `[0,1)` have binary words of the prescribed
length. Appending a string of zeros and `10` gives small interior intervals
with room between consecutive dilates.
-/

namespace Kourovka.P21_38

open GroupApproximation.HigmanThompson

namespace BinaryWord

theorem exists_chart_zero_eq_nat_div (N k : ℕ) (hk : k < 2 ^ N) :
    ∃ w : List Bool, w.length = N ∧ chart w 0 = (k : ℚ) / 2 ^ N := by
  induction N generalizing k with
  | zero =>
    have hk0 : k = 0 := by simpa using hk
    exact ⟨[], rfl, by simp [hk0]⟩
  | succ N ih =>
    by_cases hlow : k < 2 ^ N
    · obtain ⟨w, hwlen, hw⟩ := ih k hlow
      refine ⟨false :: w, by simp [hwlen], ?_⟩
      simp only [chart_cons, Bool.false_eq_true, ↓reduceIte, zero_add, hw, pow_succ]
      ring
    · have hge : 2 ^ N ≤ k := Nat.le_of_not_gt hlow
      have hsub : k - 2 ^ N < 2 ^ N := by
        rw [pow_succ] at hk
        omega
      obtain ⟨w, hwlen, hw⟩ := ih (k - 2 ^ N) hsub
      refine ⟨true :: w, by simp [hwlen], ?_⟩
      have hcast : (k : ℚ) = ((k - 2 ^ N : ℕ) : ℚ) + (2 : ℚ) ^ N := by
        exact_mod_cast (Nat.sub_add_cancel hge).symm
      simp only [chart_cons, ↓reduceIte, hw, pow_succ]
      rw [hcast]
      have hp : (2 : ℚ) ^ N ≠ 0 := by positivity
      field_simp
      ring

/-- A nonnegative level-`N` dyadic coordinate strictly below one is the
left endpoint of a length-`N` binary chart. -/
theorem exists_chart_zero_of_grid {α : ℚ} {N : ℕ}
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hgrid : α ∈ Grid 2 N) :
    ∃ w : List Bool, w.length = N ∧ chart w 0 = α := by
  obtain ⟨k, hk⟩ := hgrid
  norm_num only [Nat.cast_ofNat] at hk
  have hp : (0 : ℚ) < 2 ^ N := by positivity
  have hk0 : 0 ≤ k := by
    have h : (0 : ℚ) ≤ k := by rw [← hk]; exact mul_nonneg hα0 hp.le
    exact_mod_cast h
  have hkbound : k.toNat < 2 ^ N := by
    have h : (k : ℚ) < (2 : ℚ) ^ N := by rw [← hk]; nlinarith
    have hi : k < (2 : ℤ) ^ N := by exact_mod_cast h
    have hn : (k.toNat : ℤ) < (2 : ℤ) ^ N := by simpa using hi
    exact_mod_cast hn
  obtain ⟨w, hwlen, hw⟩ := exists_chart_zero_eq_nat_div N k.toNat hkbound
  refine ⟨w, hwlen, hw.trans ?_⟩
  apply (div_eq_iff hp.ne').mpr
  have hnat : (k.toNat : ℤ) = k := Int.toNat_of_nonneg hk0
  have hcast : (k.toNat : ℚ) = (k : ℚ) := by exact_mod_cast hnat
  exact hcast.trans hk.symm

theorem chart_replicate_false (n : ℕ) (t : ℚ) :
    chart (List.replicate n false) t = t / 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.replicate_succ, chart_cons, Bool.false_eq_true,
      ↓reduceIte, zero_add, ih, pow_succ]
    ring

/-- A narrow interval to the right of the left endpoint of `s`. -/
def rightTail (s : List Bool) (n : ℕ) : List Bool :=
  s ++ List.replicate n false ++ [true, false]

theorem rightTail_mixed (s : List Bool) (n : ℕ) :
    false ∈ rightTail s n ∧ true ∈ rightTail s n := by
  simp [rightTail]

theorem chart_rightTail (s : List Bool) (n : ℕ) (t : ℚ) :
    chart (rightTail s n) t = chart s 0 + (2 + t) / 2 ^ (s.length + n + 2) := by
  simp only [rightTail, chart_append, chart_replicate_false,
    chart_cons, chart_nil, Bool.false_eq_true, ↓reduceIte, zero_add]
  rw [chart_affine]
  simp only [pow_add]
  norm_num
  ring

end BinaryWord

end Kourovka.P21_38

#audit_axioms Kourovka.P21_38.BinaryWord.exists_chart_zero_of_grid
#audit_axioms Kourovka.P21_38.BinaryWord.chart_rightTail
