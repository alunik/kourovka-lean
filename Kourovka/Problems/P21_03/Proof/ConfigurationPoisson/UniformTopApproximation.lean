import Kourovka.Problems.P21_03.Proof.ConfigurationPoisson.UniformTopBound
import Kourovka.Problems.P21_03.Proof.ConfigurationPoisson.FactorialNormalization

/-!
# Exact uniform top-stratum approximation
-/

open Filter
open scoped Topology

namespace Kourovka213

/-- Multiplying by the exact permutation-completion factorial changes the
quadratically normalized binomial coefficient by `o(1)`, uniformly under the
degree-four witness bound. -/
theorem eventually_uniform_choose_factorial_normalization
    (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ W : ℕ, W ≤ 9 * n ^ 2 →
      |(W.choose k : ℝ) * ((n - 2 * k).factorial : ℝ) /
            (n.factorial : ℝ) -
          (W.choose k : ℝ) / (n : ℝ) ^ (2 * k)| < ε := by
  let C : ℝ := (9 : ℝ) ^ k
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  have hCpos : 0 < C := by dsimp [C]; positivity
  have hsmall : 0 < ε / (C + 1) := by positivity
  have hfactor := tendsto_factorial_normalization (2 * k)
  rw [Metric.tendsto_atTop] at hfactor
  obtain ⟨N, hN⟩ := hfactor (ε / (C + 1)) hsmall
  filter_upwards [eventually_ge_atTop N, eventually_ge_atTop 1] with n hnN hn
  intro W hW
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnpow : (0 : ℝ) < (n : ℝ) ^ (2 * k) := by positivity
  have hclose :
      |(n : ℝ) ^ (2 * k) * ((n - 2 * k).factorial : ℝ) /
          (n.factorial : ℝ) - 1| < ε / (C + 1) := by
    simpa only [Real.dist_eq] using hN n hnN
  have hchooseNat : W.choose k ≤ W ^ k := Nat.choose_le_pow W k
  have hchoosePow : (W.choose k : ℝ) ≤ (W : ℝ) ^ k := by
    exact_mod_cast hchooseNat
  have hWR : (W : ℝ) ≤ 9 * (n : ℝ) ^ 2 := by exact_mod_cast hW
  have hchooseBound : (W.choose k : ℝ) ≤
      C * (n : ℝ) ^ (2 * k) := by
    calc
      (W.choose k : ℝ) ≤ (W : ℝ) ^ k := hchoosePow
      _ ≤ (9 * (n : ℝ) ^ 2) ^ k := by gcongr
      _ = C * (n : ℝ) ^ (2 * k) := by
        dsimp [C]
        rw [mul_pow, ← pow_mul]
  have hx0 : 0 ≤ (W.choose k : ℝ) / (n : ℝ) ^ (2 * k) := by positivity
  have hxC : (W.choose k : ℝ) / (n : ℝ) ^ (2 * k) ≤ C := by
    apply (div_le_iff₀ hnpow).2
    simpa [mul_comm] using hchooseBound
  have heq :
      (W.choose k : ℝ) * ((n - 2 * k).factorial : ℝ) /
            (n.factorial : ℝ) -
          (W.choose k : ℝ) / (n : ℝ) ^ (2 * k) =
        ((W.choose k : ℝ) / (n : ℝ) ^ (2 * k)) *
          ((n : ℝ) ^ (2 * k) * ((n - 2 * k).factorial : ℝ) /
            (n.factorial : ℝ) - 1) := by
    have hnfac : (n.factorial : ℝ) ≠ 0 := by positivity
    field_simp
  rw [heq, abs_mul, abs_of_nonneg hx0]
  calc
    (W.choose k : ℝ) / (n : ℝ) ^ (2 * k) *
          |(n : ℝ) ^ (2 * k) * ((n - 2 * k).factorial : ℝ) /
              (n.factorial : ℝ) - 1| ≤
        C * |(n : ℝ) ^ (2 * k) * ((n - 2 * k).factorial : ℝ) /
              (n.factorial : ℝ) - 1| := by
      exact mul_le_mul_of_nonneg_right hxC (abs_nonneg _)
    _ < C * (ε / (C + 1)) := mul_lt_mul_of_pos_left hclose hCpos
    _ < ε := by
      rw [← mul_div_assoc]
      apply (div_lt_iff₀ (by positivity : 0 < C + 1)).2
      nlinarith

/-- Replacing the quadratic normalization `n^2` by the collision-mean
normalization `n(n-1)` changes every fixed power by `o(1)`, uniformly under
the degree-four witness bound. -/
theorem eventually_uniform_collision_denominator_normalization
    (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ W : ℕ, W ≤ 9 * n ^ 2 →
      |((W : ℝ) / (n : ℝ) ^ 2) ^ k / (k.factorial : ℝ) -
          ((W : ℝ) / ((n : ℝ) * (n - 1))) ^ k /
            (k.factorial : ℝ)| < ε := by
  let C : ℝ := (9 : ℝ) ^ k
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  have hCpos : 0 < C := by dsimp [C]; positivity
  have hsmall : 0 < ε / (C + 1) := by positivity
  have hratio : Tendsto
      (fun n : ℕ => (n : ℝ) / (n - 1 : ℝ)) atTop (nhds 1) := by
    simpa [sub_eq_add_neg] using
      (tendsto_natCast_div_add_atTop (-1 : ℝ))
  have hratioPow : Tendsto
      (fun n : ℕ => ((n : ℝ) / (n - 1 : ℝ)) ^ k) atTop (nhds 1) := by
    simpa using hratio.pow k
  rw [Metric.tendsto_atTop] at hratioPow
  obtain ⟨N, hN⟩ := hratioPow (ε / (C + 1)) hsmall
  filter_upwards [eventually_ge_atTop N, eventually_ge_atTop 2] with n hnN hn
  intro W hW
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnOneR : (0 : ℝ) < (n : ℝ) - 1 := by
    exact sub_pos.mpr (by exact_mod_cast (show 1 < n by omega))
  have hnpow : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
  have hclose : |((n : ℝ) / (n - 1 : ℝ)) ^ k - 1| < ε / (C + 1) := by
    simpa only [Real.dist_eq] using hN n hnN
  have hWR : (W : ℝ) ≤ 9 * (n : ℝ) ^ 2 := by exact_mod_cast hW
  have hbase : (W : ℝ) / (n : ℝ) ^ 2 ≤ 9 := by
    apply (div_le_iff₀ hnpow).2
    simpa [mul_comm] using hWR
  have hpowBase : ((W : ℝ) / (n : ℝ) ^ 2) ^ k ≤ C := by
    dsimp [C]
    gcongr
  have hfacOne : (1 : ℝ) ≤ (k.factorial : ℝ) := by
    exact_mod_cast k.factorial_pos
  have hx0 : 0 ≤
      ((W : ℝ) / (n : ℝ) ^ 2) ^ k / (k.factorial : ℝ) := by
    positivity
  have hxC :
      ((W : ℝ) / (n : ℝ) ^ 2) ^ k / (k.factorial : ℝ) ≤ C := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < k.factorial)).2
    exact hpowBase.trans (le_mul_of_one_le_right hC0 hfacOne)
  have hbaseEq :
      ((W : ℝ) / ((n : ℝ) * (n - 1))) ^ k /
            (k.factorial : ℝ) =
        (((W : ℝ) / (n : ℝ) ^ 2) ^ k / (k.factorial : ℝ)) *
          ((n : ℝ) / (n - 1 : ℝ)) ^ k := by
    have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
    have hnOne0 : (n : ℝ) - 1 ≠ 0 := ne_of_gt hnOneR
    have hscalar :
        (W : ℝ) / ((n : ℝ) * (n - 1)) =
          ((W : ℝ) / (n : ℝ) ^ 2) *
            ((n : ℝ) / (n - 1 : ℝ)) := by
      field_simp
    rw [hscalar, mul_pow]
    ring
  rw [hbaseEq]
  have heq :
      ((W : ℝ) / (n : ℝ) ^ 2) ^ k / (k.factorial : ℝ) -
          ((W : ℝ) / (n : ℝ) ^ 2) ^ k / (k.factorial : ℝ) *
            ((n : ℝ) / (n - 1 : ℝ)) ^ k =
        (((W : ℝ) / (n : ℝ) ^ 2) ^ k / (k.factorial : ℝ)) *
          (1 - ((n : ℝ) / (n - 1 : ℝ)) ^ k) := by ring
  rw [heq, abs_mul, abs_of_nonneg hx0, abs_sub_comm]
  calc
    ((W : ℝ) / (n : ℝ) ^ 2) ^ k / (k.factorial : ℝ) *
          |((n : ℝ) / (n - 1 : ℝ)) ^ k - 1| ≤
        C * |((n : ℝ) / (n - 1 : ℝ)) ^ k - 1| := by
      exact mul_le_mul_of_nonneg_right hxC (abs_nonneg _)
    _ < C * (ε / (C + 1)) := mul_lt_mul_of_pos_left hclose hCpos
    _ < ε := by
      rw [← mul_div_assoc]
      apply (div_lt_iff₀ (by positivity : 0 < C + 1)).2
      nlinarith

/-- The exact top-support contribution has the required Poisson main term,
uniformly for every possible degree-four witness count. -/
theorem eventually_uniform_top_support_term
    (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ W : ℕ, W ≤ 9 * n ^ 2 →
      |(W.choose k : ℝ) * ((n - 2 * k).factorial : ℝ) /
            (n.factorial : ℝ) -
          ((W : ℝ) / ((n : ℝ) * (n - 1))) ^ k /
            (k.factorial : ℝ)| < ε := by
  have hthird : 0 < ε / 3 := by positivity
  have hfactor := eventually_uniform_choose_factorial_normalization k (ε / 3) hthird
  have hchoose := eventually_uniform_choose_density k (ε / 3) hthird
  have hdenominator :=
    eventually_uniform_collision_denominator_normalization k (ε / 3) hthird
  filter_upwards [hfactor, hchoose, hdenominator] with n hnFactor hnChoose hnDenominator
  intro W hW
  have hf := hnFactor W hW
  have hc := hnChoose W hW
  have hd := hnDenominator W hW
  let A : ℝ := (W.choose k : ℝ) * ((n - 2 * k).factorial : ℝ) /
    (n.factorial : ℝ)
  let C : ℝ := (W.choose k : ℝ) / (n : ℝ) ^ (2 * k)
  let D : ℝ := ((W : ℝ) / (n : ℝ) ^ 2) ^ k / (k.factorial : ℝ)
  let B : ℝ := ((W : ℝ) / ((n : ℝ) * (n - 1))) ^ k /
    (k.factorial : ℝ)
  have hf' : |A - C| < ε / 3 := by simpa [A, C] using hf
  have hc' : |C - D| < ε / 3 := by simpa [C, D] using hc
  have hd' : |D - B| < ε / 3 := by simpa [D, B] using hd
  change |A - B| < ε
  calc
    |A - B| ≤ |A - C| + |C - B| := abs_sub_le A C B
    _ ≤ |A - C| + (|C - D| + |D - B|) := by
      gcongr
      exact abs_sub_le C D B
    _ < ε := by linarith

end Kourovka213
