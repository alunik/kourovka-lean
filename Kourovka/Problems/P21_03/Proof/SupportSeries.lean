import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Data.Nat.Factorial.Basic

/-!
# Summability of the support majorant

After the forest and centralizer estimates are combined, the non-core error is bounded
by a constant times this rapidly decaying series.
-/

open scoped BigOperators Topology

namespace Kourovka213

noncomputable def supportSeriesTerm (C s : ℕ) : ℝ :=
  (C : ℝ) ^ s / (s : ℝ) ^ ((s - 1) / 2)

theorem self_le_two_pow_pred (r : ℕ) (hr : 1 ≤ r) : r ≤ 2 ^ (r - 1) := by
  induction r with
  | zero => omega
  | succ r ih =>
      by_cases hr0 : r = 0
      · simp [hr0]
      · have hr1 : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr hr0
        calc
          r + 1 ≤ 2 * r := by omega
          _ ≤ 2 * 2 ^ (r - 1) := Nat.mul_le_mul_left 2 (ih hr1)
          _ = 2 ^ ((r - 1) + 1) := (pow_succ' 2 (r - 1)).symm
          _ = 2 ^ r := by congr 1 <;> omega
          _ = 2 ^ ((r + 1) - 1) := by rw [Nat.add_sub_cancel]

theorem factorial_le_two_mul_self_pow_pred (r : ℕ) :
    r.factorial ≤ (2 * r) ^ (r - 1) := by
  obtain rfl | hr := r.eq_zero_or_pos
  · simp
  have hrpow := self_le_two_pow_pred r hr
  calc
    r.factorial ≤ r ^ r := Nat.factorial_le_pow r
    _ = r ^ (r - 1) * r := by
      nth_rewrite 2 [show r = (r - 1) + 1 by omega]
      rw [pow_succ]
    _ ≤ r ^ (r - 1) * 2 ^ (r - 1) := Nat.mul_le_mul_left _ hrpow
    _ = (2 * r) ^ (r - 1) := by rw [Nat.mul_pow]; ac_rfl

/-- The coefficient series converges for every fixed exponential base. -/
theorem summable_supportSeriesTerm (C : ℕ) :
    Summable (supportSeriesTerm C) := by
  apply Summable.even_add_odd
  · apply Summable.of_nonneg_of_le
      (fun r => div_nonneg (by positivity) (by positivity))
      (fun r => ?_)
      (Real.summable_pow_div_factorial ((C : ℝ) ^ 2))
    have hden : (r.factorial : ℝ) ≤
        ((2 * r : ℕ) : ℝ) ^ (((2 * r : ℕ) - 1) / 2) := by
      have hexp : ((2 * r : ℕ) - 1) / 2 = r - 1 := by omega
      rw [hexp]
      norm_cast
      exact factorial_le_two_mul_self_pow_pred r
    calc
      (C : ℝ) ^ (2 * r) / ((2 * r : ℕ) : ℝ) ^ (((2 * r : ℕ) - 1) / 2) ≤
          (C : ℝ) ^ (2 * r) / r.factorial := by
        exact div_le_div_of_nonneg_left (by positivity) (by positivity) hden
      _ = ((C : ℝ) ^ 2) ^ r / r.factorial := by rw [← pow_mul]
  · apply Summable.of_nonneg_of_le
      (fun r => div_nonneg (by positivity) (by positivity))
      (fun r => ?_)
      ((Real.summable_pow_div_factorial ((C : ℝ) ^ 2)).mul_left (C : ℝ))
    have hdenNat : r.factorial ≤ (2 * r + 1) ^ r := by
      exact (Nat.factorial_le_pow r).trans
        (Nat.pow_le_pow_left (by omega : r ≤ 2 * r + 1) r)
    have hden : (r.factorial : ℝ) ≤
        ((2 * r + 1 : ℕ) : ℝ) ^ (((2 * r + 1 : ℕ) - 1) / 2) := by
      have hexp : ((2 * r + 1 : ℕ) - 1) / 2 = r := by omega
      rw [hexp]
      norm_cast
    calc
      (C : ℝ) ^ (2 * r + 1) /
          ((2 * r + 1 : ℕ) : ℝ) ^ (((2 * r + 1 : ℕ) - 1) / 2) ≤
          (C : ℝ) ^ (2 * r + 1) / r.factorial := by
        exact div_le_div_of_nonneg_left (by positivity) (by positivity) hden
      _ = (C : ℝ) * (((C : ℝ) ^ 2) ^ r / r.factorial) := by
        rw [pow_add, pow_one, ← pow_mul]
        ring

end Kourovka213
