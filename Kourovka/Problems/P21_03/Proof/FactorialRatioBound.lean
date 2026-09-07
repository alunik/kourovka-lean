import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Nat.Choose.Bounds

/-!
# A uniform falling-factorial bound

The class-sum estimate needs a constant-base replacement for
`n ^ s * (n-s)! / n!`.  The final theorem gives the convenient base `3`.
-/

open scoped BigOperators

namespace Kourovka213

theorem pow_self_le_three_pow_mul_factorial (s : ℕ) :
    s ^ s ≤ 3 ^ s * s.factorial := by
  have hreal : (s : ℝ) ^ s ≤ (3 : ℝ) ^ s * s.factorial := by
    obtain rfl | hs := s.eq_zero_or_pos
    · norm_num
    have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
    have hsqrt : (1 : ℝ) ≤ Real.sqrt (2 * Real.pi * s) := by
      rw [Real.le_sqrt (by norm_num) (by positivity)]
      have hpi : (3 : ℝ) ≤ Real.pi := Real.pi_gt_three.le
      have hsone : (1 : ℝ) ≤ s := by exact_mod_cast hs
      calc
        (1 : ℝ) ^ 2 ≤ 2 * 3 * 1 := by norm_num
        _ ≤ 2 * Real.pi * 1 := by gcongr
        _ ≤ 2 * Real.pi * s := by gcongr
    have hbase : (s : ℝ) / 3 ≤ (s : ℝ) / Real.exp 1 := by
      exact div_le_div_of_nonneg_left hs0.le (Real.exp_pos 1) Real.exp_one_lt_three.le
    have hsmall : ((s : ℝ) / 3) ^ s ≤ (s.factorial : ℝ) := by
      calc
        ((s : ℝ) / 3) ^ s ≤ ((s : ℝ) / Real.exp 1) ^ s :=
          pow_le_pow_left₀ (by positivity) hbase _
        _ ≤ Real.sqrt (2 * Real.pi * s) * ((s : ℝ) / Real.exp 1) ^ s :=
          le_mul_of_one_le_left (by positivity) hsqrt
        _ ≤ (s.factorial : ℝ) := Stirling.le_factorial_stirling s
    calc
      (s : ℝ) ^ s = (3 : ℝ) ^ s * ((s : ℝ) / 3) ^ s := by
        rw [div_pow]
        field_simp
      _ ≤ (3 : ℝ) ^ s * s.factorial :=
        mul_le_mul_of_nonneg_left hsmall (by positivity)
  exact_mod_cast hreal

theorem pow_le_pow_mul_choose (n s : ℕ) (hsn : s ≤ n) :
    n ^ s ≤ s ^ s * n.choose s := by
  have hprod : n ^ s * s.factorial ≤ s ^ s * n.descFactorial s := by
    calc
      n ^ s * s.factorial =
          (∏ i ∈ Finset.range s, n) * (∏ i ∈ Finset.range s, (s - i)) := by
        simp [← Nat.descFactorial_eq_prod_range, Nat.descFactorial_self]
      _ = ∏ i ∈ Finset.range s, n * (s - i) := Finset.prod_mul_distrib.symm
      _ ≤ ∏ i ∈ Finset.range s, s * (n - i) := by
        apply Finset.prod_le_prod
        · exact fun _ _ => Nat.zero_le _
        · intro i hi
          have his : i < s := Finset.mem_range.mp hi
          have hmul : s * i ≤ n * i := Nat.mul_le_mul_right i hsn
          calc
            n * (s - i) = n * s - n * i := Nat.mul_sub_left_distrib n s i
            _ ≤ n * s - s * i := Nat.sub_le_sub_left hmul (n * s)
            _ = s * (n - i) := by
              rw [Nat.mul_sub_left_distrib, Nat.mul_comm n s]
      _ = (∏ i ∈ Finset.range s, s) * (∏ i ∈ Finset.range s, (n - i)) :=
        Finset.prod_mul_distrib
      _ = s ^ s * n.descFactorial s := by
        simp [← Nat.descFactorial_eq_prod_range]
  rw [Nat.descFactorial_eq_factorial_mul_choose] at hprod
  apply Nat.le_of_mul_le_mul_right (c := s.factorial) ?_ s.factorial_pos
  simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hprod

/-- Uniform constant-base comparison with the falling factorial. -/
theorem pow_mul_factorial_sub_le_three_pow_mul_factorial
    (n s : ℕ) (hsn : s ≤ n) :
    n ^ s * (n - s).factorial ≤ 3 ^ s * n.factorial := by
  calc
    n ^ s * (n - s).factorial ≤
        (s ^ s * n.choose s) * (n - s).factorial :=
      Nat.mul_le_mul_right _ (pow_le_pow_mul_choose n s hsn)
    _ ≤ (3 ^ s * s.factorial * n.choose s) * (n - s).factorial := by
      gcongr
      exact pow_self_le_three_pow_mul_factorial s
    _ = 3 ^ s * n.factorial := by
      rw [← Nat.choose_mul_factorial_mul_factorial hsn]
      ac_rfl

end Kourovka213
