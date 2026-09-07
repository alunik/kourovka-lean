import Kourovka.Problems.P21_03.Proof.FactorialRatioBound
import Mathlib.Analysis.SpecialFunctions.Choose

/-!
# Uniform approximation of the top support stratum

This file supplies the quantitative analytic estimate needed to replace the
exact top-stratum count by the corresponding Poisson moment.  All estimates
are uniform in the witness count, subject only to its quadratic degree bound.
-/

open Filter
open scoped Topology

namespace Kourovka213

/-- Uniformly for `W = O(n^2)`, the normalized binomial coefficient is
approximated by the corresponding normalized power. -/
theorem eventually_uniform_choose_density (j : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ W : ℕ, W ≤ 9 * n ^ 2 →
      |((W.choose j : ℕ) : ℝ) / (n : ℝ) ^ (2 * j) -
          ((W : ℝ) / (n : ℝ) ^ 2) ^ j / (j.factorial : ℝ)| < ε := by
  obtain rfl | k := j
  · filter_upwards [eventually_ge_atTop 1] with n hn
    intro W hW
    simpa using hε
  let C : ℝ := (((k + 1 : ℕ) ^ (k + 1) : ℕ) : ℝ) /
      ((k + 1).factorial : ℝ) +
      ((k + 1 : ℝ) ^ 2 * 9 ^ k) / ((k + 1).factorial : ℝ)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hzero : Tendsto (fun n : ℕ => C / (n : ℝ) ^ 2) atTop (nhds 0) := by
    simpa only [Function.comp_def, Nat.cast_pow] using
      (tendsto_const_div_atTop_nhds_zero_nat C).comp
        (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0))
  rw [Metric.tendsto_atTop] at hzero
  obtain ⟨N, hN⟩ := hzero ε hε
  filter_upwards [eventually_ge_atTop N, eventually_ge_atTop 1] with n hnN hn
  intro W hW
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hden : (0 : ℝ) < (n : ℝ) ^ (2 * (k + 1)) := by positivity
  have hfac : (0 : ℝ) < ((k + 1).factorial : ℕ) := by positivity
  have hchooseUpper : (W.choose (k + 1) : ℝ) ≤
      (W : ℝ) ^ (k + 1) / ((k + 1).factorial : ℝ) :=
    Nat.choose_le_pow_div (α := ℝ) (k + 1) W
  have hmainNonneg : 0 ≤
      ((W : ℝ) / (n : ℝ) ^ 2) ^ (k + 1) /
          ((k + 1).factorial : ℝ) -
        (W.choose (k + 1) : ℝ) / (n : ℝ) ^ (2 * (k + 1)) := by
    rw [div_pow, ← pow_mul]
    calc
      0 ≤ ((W : ℝ) ^ (k + 1) / ((k + 1).factorial : ℝ) -
            (W.choose (k + 1) : ℝ)) / (n : ℝ) ^ (2 * (k + 1)) :=
        div_nonneg (sub_nonneg.mpr hchooseUpper) hden.le
      _ = (W : ℝ) ^ (k + 1) / (n : ℝ) ^ (2 * (k + 1)) /
            ((k + 1).factorial : ℝ) -
          (W.choose (k + 1) : ℝ) / (n : ℝ) ^ (2 * (k + 1)) := by
        ring
  rw [abs_sub_comm, abs_of_nonneg hmainNonneg]
  have hbound :
      ((W : ℝ) / (n : ℝ) ^ 2) ^ (k + 1) /
            ((k + 1).factorial : ℝ) -
          (W.choose (k + 1) : ℝ) / (n : ℝ) ^ (2 * (k + 1)) ≤
        C / (n : ℝ) ^ 2 := by
    by_cases hsmall : W < k + 1
    · rw [Nat.choose_eq_zero_of_lt hsmall, Nat.cast_zero, zero_div, sub_zero]
      have hWR : (W : ℝ) ≤ k + 1 := by exact_mod_cast hsmall.le
      have hpowW : (W : ℝ) ^ (k + 1) ≤ (k + 1 : ℝ) ^ (k + 1) := by
        gcongr
      rw [div_pow, ← pow_mul]
      have hpowN : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ (2 * (k + 1)) := by
        rw [show 2 * (k + 1) = 2 + 2 * k by omega, pow_add]
        have hone : (1 : ℝ) ≤ (n : ℝ) ^ (2 * k) :=
          one_le_pow₀ (by exact_mod_cast hn)
        nlinarith
      calc
        (W : ℝ) ^ (k + 1) / (n : ℝ) ^ (2 * (k + 1)) /
              ((k + 1).factorial : ℝ) ≤
            (k + 1 : ℝ) ^ (k + 1) /
              (n : ℝ) ^ (2 * (k + 1)) /
                ((k + 1).factorial : ℝ) := by gcongr
        _ ≤ (k + 1 : ℝ) ^ (k + 1) / (n : ℝ) ^ 2 /
                ((k + 1).factorial : ℝ) := by gcongr
        _ ≤ C / (n : ℝ) ^ 2 := by
          dsimp [C]
          have hnonneg : 0 ≤
              ((k + 1 : ℝ) ^ 2 * 9 ^ k) / ((k + 1).factorial : ℝ) := by
            positivity
          calc
            _ = ((((k + 1 : ℕ) ^ (k + 1) : ℕ) : ℝ) /
                  ((k + 1).factorial : ℝ)) / (n : ℝ) ^ 2 := by
              push_cast
              ring
            _ ≤ (((((k + 1 : ℕ) ^ (k + 1) : ℕ) : ℝ) /
                    ((k + 1).factorial : ℝ)) +
                  ((k + 1 : ℝ) ^ 2 * 9 ^ k) /
                    ((k + 1).factorial : ℝ)) / (n : ℝ) ^ 2 := by
              exact div_le_div_of_nonneg_right
                (le_add_of_nonneg_right hnonneg) (by positivity)
    · have hkW : k + 1 ≤ W := Nat.le_of_not_gt hsmall
      have hlower : (((W + 1 - (k + 1)) ^ (k + 1) : ℕ) : ℝ) /
            ((k + 1).factorial : ℝ) ≤ (W.choose (k + 1) : ℝ) := by
        simpa only [Nat.cast_pow] using
          (Nat.pow_le_choose (α := ℝ) (k + 1) W)
      have hsubcast : ((W + 1 - (k + 1) : ℕ) : ℝ) = (W : ℝ) - k := by
        rw [Nat.cast_sub (by omega : k + 1 ≤ W + 1)]
        push_cast
        ring
      have hpowDiff :
          (W : ℝ) ^ (k + 1) - (W - k : ℝ) ^ (k + 1) ≤
            (k + 1 : ℝ) ^ 2 * (W : ℝ) ^ k := by
        have hWnonneg : 0 ≤ (W : ℝ) := by positivity
        have hWsubnonneg : 0 ≤ (W : ℝ) - k := by
          exact sub_nonneg.mpr (by exact_mod_cast (show k ≤ W by omega))
        have hpowsub : (W - k : ℝ) ^ (k + 1) ≤ (W : ℝ) ^ (k + 1) := by
          exact pow_le_pow_left₀ hWsubnonneg
            (sub_le_self _ (by positivity)) _
        have habs := abs_pow_sub_pow_le (W : ℝ) (W - k : ℝ) (k + 1)
        have hdiffabs : |(W : ℝ) - ((W : ℝ) - k)| = (k : ℝ) := by
          rw [show (W : ℝ) - ((W : ℝ) - k) = k by ring,
            abs_of_nonneg (by positivity)]
        have hmaxabs : max |(W : ℝ)| |(W : ℝ) - k| = (W : ℝ) := by
          rw [abs_of_nonneg hWnonneg, abs_of_nonneg hWsubnonneg,
            max_eq_left (sub_le_self _ (by positivity))]
        rw [abs_of_nonneg (sub_nonneg.mpr hpowsub), hdiffabs, hmaxabs,
          Nat.add_sub_cancel] at habs
        calc
          _ ≤ (k : ℝ) * (k + 1) * (W : ℝ) ^ k := by
            simpa only [Nat.cast_add, Nat.cast_one] using habs
          _ ≤ (k + 1 : ℝ) ^ 2 * (W : ℝ) ^ k := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            nlinarith [show (0 : ℝ) ≤ k by positivity]
      have hWR : (W : ℝ) ≤ 9 * (n : ℝ) ^ 2 := by exact_mod_cast hW
      have hpowWR : (W : ℝ) ^ k ≤ (9 * (n : ℝ) ^ 2) ^ k := by gcongr
      rw [div_pow, ← pow_mul]
      rw [Nat.cast_pow] at hlower
      rw [hsubcast] at hlower
      calc
        (W : ℝ) ^ (k + 1) / (n : ℝ) ^ (2 * (k + 1)) /
                ((k + 1).factorial : ℝ) -
              (W.choose (k + 1) : ℝ) / (n : ℝ) ^ (2 * (k + 1)) =
            ((W : ℝ) ^ (k + 1) / ((k + 1).factorial : ℝ) -
              (W.choose (k + 1) : ℝ)) /
                (n : ℝ) ^ (2 * (k + 1)) := by ring
        _ ≤ ((W : ℝ) ^ (k + 1) / ((k + 1).factorial : ℝ) -
              (W - k : ℝ) ^ (k + 1) / ((k + 1).factorial : ℝ)) /
                (n : ℝ) ^ (2 * (k + 1)) := by gcongr
        _ = ((W : ℝ) ^ (k + 1) - (W - k : ℝ) ^ (k + 1)) /
              ((k + 1).factorial : ℝ) / (n : ℝ) ^ (2 * (k + 1)) := by
          ring
        _ ≤ ((k + 1 : ℝ) ^ 2 * (W : ℝ) ^ k) /
              ((k + 1).factorial : ℝ) / (n : ℝ) ^ (2 * (k + 1)) := by
          gcongr
        _ ≤ ((k + 1 : ℝ) ^ 2 * (9 * (n : ℝ) ^ 2) ^ k) /
              ((k + 1).factorial : ℝ) / (n : ℝ) ^ (2 * (k + 1)) := by
          gcongr
        _ ≤ C / (n : ℝ) ^ 2 := by
          have heq :
              ((k + 1 : ℝ) ^ 2 * (9 * (n : ℝ) ^ 2) ^ k) /
                    ((k + 1).factorial : ℝ) / (n : ℝ) ^ (2 * (k + 1)) =
                (((k + 1 : ℝ) ^ 2 * 9 ^ k) /
                    ((k + 1).factorial : ℝ)) / (n : ℝ) ^ 2 := by
            rw [mul_pow, ← pow_mul]
            field_simp
            ring
          rw [heq]
          dsimp [C]
          exact div_le_div_of_nonneg_right
            (le_add_of_nonneg_left (by positivity)) (by positivity)
  exact hbound.trans_lt (by
    have hd := hN n hnN
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg hC (by positivity))] at hd
    exact hd)

end Kourovka213
