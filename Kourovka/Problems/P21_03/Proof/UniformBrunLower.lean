import Kourovka.Problems.P21_03.Proof.ConfigurationPoisson.ConfigurationLimit
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Topology.Algebra.Order.Floor

/-!
# Uniform lower half of the bounded-degree Brun sieve

This file is the analytic uniformization layer.  Its sole combinatorial input is
uniform convergence, for each fixed order, of the collision binomial moment to the
corresponding power of the (varying) collision mean.  A fixed odd Bonferroni
truncation, together with a uniform exponential-tail estimate on means in `[0,5]`,
then gives the lower bound needed for Problem 21.3.
-/

open Filter Finset
open scoped BigOperators Topology

namespace Kourovka213

/-- Uniform fixed-order binomial-moment approximation for all bounded partitions. -/
def UniformCollisionMomentApproximation : Prop :=
  ∀ (j : ℕ) (ε : ℝ), 0 < ε → ∀ᶠ n : ℕ in atTop,
    ∀ P Q : BoundedPartition n,
      |normalizedBinomialMoment (collisionCount P Q) j -
          collisionMean P Q ^ j / (j.factorial : ℝ)| < ε

/-- Uniform Taylor remainder for `exp (-μ)` on `0 ≤ μ ≤ 5`. -/
theorem abs_exp_neg_sub_poissonPartial_le
    {μ : ℝ} (hμ0 : 0 ≤ μ) (hμ5 : μ ≤ 5)
    {m : ℕ} (hm : 10 ≤ m) :
    |Real.exp (-μ) - ∑ j ∈ range m, (-μ) ^ j / (j.factorial : ℝ)| ≤
      2 * 5 ^ m / (m.factorial : ℝ) := by
  have hmpos : (0 : ℝ) < m + 1 := by positivity
  have hcond : ‖((-μ : ℝ) : ℂ)‖ / (m.succ : ℝ) ≤ 1 / 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_nonneg hμ0]
    simp only [Nat.cast_succ]
    apply (div_le_iff₀ hmpos).2
    nlinarith [show (10 : ℝ) ≤ m by exact_mod_cast hm]
  have h := Complex.exp_bound' (x := ((-μ : ℝ) : ℂ)) hcond
  have hreal :
      |Real.exp (-μ) - ∑ j ∈ range m, (-μ) ^ j / (j.factorial : ℝ)| ≤
        μ ^ m / (m.factorial : ℝ) * 2 := by
    rw [← Complex.ofReal_exp] at h
    norm_cast at h
    simpa [Real.norm_eq_abs, abs_of_nonneg hμ0] using h
  calc
    _ ≤ μ ^ m / (m.factorial : ℝ) * 2 := hreal
    _ ≤ 5 ^ m / (m.factorial : ℝ) * 2 := by gcongr
    _ = 2 * 5 ^ m / (m.factorial : ℝ) := by ring

/-- The elementary upper cap for the collision mean. -/
noncomputable def collisionMeanCap (n : ℕ) : ℝ :=
  (9 / 2 : ℝ) * n / (n - 1)

theorem tendsto_collisionMeanCap :
    Tendsto collisionMeanCap atTop (nhds (9 / 2 : ℝ)) := by
  have hratio : Tendsto (fun n : ℕ => (n : ℝ) / (n - 1 : ℝ)) atTop (nhds 1) := by
    simpa [sub_eq_add_neg] using tendsto_natCast_div_add_atTop (-1 : ℝ)
  have hprod :
      Tendsto (fun n : ℕ => (9 / 2 : ℝ) * ((n : ℝ) / (n - 1 : ℝ)))
        atTop (nhds ((9 / 2 : ℝ) * 1)) :=
    (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (9 / 2 : ℝ)) atTop (nhds (9 / 2 : ℝ))).mul hratio
  change Tendsto (fun n : ℕ => (9 / 2 : ℝ) * n / (n - 1))
    atTop (nhds (9 / 2 : ℝ))
  simpa only [mul_div_assoc, mul_one] using hprod

theorem collisionMean_nonneg (P Q : BoundedPartition n) :
    0 ≤ collisionMean P Q := by
  unfold collisionMean
  positivity

theorem collisionMean_le_five (P Q : BoundedPartition n) (hn : 10 ≤ n) :
    collisionMean P Q ≤ 5 := by
  have hcap := collisionMean_le P Q (by omega)
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
    linarith
  apply hcap.trans
  apply (div_le_iff₀ hn1).2
  have hnR : (10 : ℝ) ≤ n := by exact_mod_cast hn
  nlinarith

/-- Uniform fixed-moment control gives uniform control of every fixed
Bonferroni polynomial. -/
theorem eventually_normalizedBonferroni_sub_poissonPartial_abs_lt
    (hmoment : UniformCollisionMomentApproximation)
    (m : ℕ) (hm : 0 < m) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ P Q : BoundedPartition n,
      |normalizedBonferroni (collisionCount P Q) (m - 1) -
          ∑ j ∈ range m, poissonAlternatingTerm (collisionMean P Q) j| < ε := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hsmall : 0 < ε / (2 * m) := by positivity
  have hall : ∀ᶠ n : ℕ in atTop, ∀ j ∈ range m,
      ∀ P Q : BoundedPartition n,
        |normalizedBinomialMoment (collisionCount P Q) j -
          collisionMean P Q ^ j / (j.factorial : ℝ)| < ε / (2 * m) := by
    exact (Filter.eventually_all_finset (range m)).2 fun j _hj ↦
      hmoment j (ε / (2 * m)) hsmall
  filter_upwards [hall] with n hn
  intro P Q
  unfold normalizedBonferroni poissonAlternatingTerm
  rw [Nat.sub_add_cancel hm, ← Finset.sum_sub_distrib]
  calc
    |∑ j ∈ range m,
        ((-1 : ℝ) ^ j * normalizedBinomialMoment (collisionCount P Q) j -
          (-collisionMean P Q) ^ j / (j.factorial : ℝ))| ≤
        ∑ j ∈ range m,
          |(-1 : ℝ) ^ j * normalizedBinomialMoment (collisionCount P Q) j -
            (-collisionMean P Q) ^ j / (j.factorial : ℝ)| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ range m, ε / (2 * m) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjbound := (hn j hj P Q).le
      convert hjbound using 1
      rw [neg_pow]
      ring_nf
      rw [← sub_mul, abs_mul]
      simp
    _ = m * (ε / (2 * m)) := by simp
    _ < ε := by
      have heq : (m : ℝ) * (ε / (2 * m)) = ε / 2 := by
        field_simp
      rw [heq]
      linarith

/-- Uniform fixed-order moment asymptotics imply the eventual uniform lower
bound for zero collisions. -/
theorem uniformConfigurationLowerAsymptotic_of_moments
    (hmoment : UniformCollisionMomentApproximation) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ∀ P Q : BoundedPartition n,
        Real.exp (-(9 : ℝ) / 2) - ε ≤
          normalizedZeroCount (collisionCount P Q) := by
  intro ε hε
  have hquarter : 0 < ε / 4 := by positivity
  have htailT : Tendsto
      (fun m : ℕ => 2 * (5 : ℝ) ^ m / (m.factorial : ℝ))
      atTop (nhds 0) := by
    simpa [mul_div_assoc] using
      (FloorSemiring.tendsto_pow_div_factorial_atTop (5 : ℝ)).const_mul 2
  rw [Metric.tendsto_atTop] at htailT
  obtain ⟨Ntail, hNtail⟩ := htailT (ε / 4) hquarter
  let r : ℕ := max 5 Ntail
  let m : ℕ := 2 * r + 2
  have hmpos : 0 < m := by simp [m]
  have hmten : 10 ≤ m := by dsimp [m, r]; omega
  have hNtailm : Ntail ≤ m := by dsimp [m, r]; omega
  have htail : 2 * (5 : ℝ) ^ m / (m.factorial : ℝ) < ε / 4 := by
    have hdist := hNtail m hNtailm
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hdist
    exact hdist
  have hBF := eventually_normalizedBonferroni_sub_poissonPartial_abs_lt
    hmoment m hmpos hquarter
  have hcapT : Tendsto (fun n : ℕ => Real.exp (-collisionMeanCap n))
      atTop (nhds (Real.exp (-(9 : ℝ) / 2))) := by
    have hneg := tendsto_collisionMeanCap.neg
    have hexp := (Real.continuous_exp.tendsto (-(9 / 2 : ℝ))).comp hneg
    change Tendsto (Real.exp ∘ fun n : ℕ => -collisionMeanCap n)
      atTop (nhds (Real.exp (-(9 : ℝ) / 2)))
    convert hexp using 1 <;> ring
  have hcapLower : ∀ᶠ n : ℕ in atTop,
      Real.exp (-(9 : ℝ) / 2) - ε / 4 <
        Real.exp (-collisionMeanCap n) := by
    exact hcapT.eventually (Ioi_mem_nhds (sub_lt_self _ hquarter))
  filter_upwards [hBF, hcapLower, eventually_ge_atTop 10] with n hnBF hnCap hnTen
  intro P Q
  let μ := collisionMean P Q
  let ideal : ℝ := ∑ j ∈ range m, poissonAlternatingTerm μ j
  let actual : ℝ := normalizedBonferroni (collisionCount P Q) (m - 1)
  have hμ0 : 0 ≤ μ := collisionMean_nonneg P Q
  have hμ5 : μ ≤ 5 := collisionMean_le_five P Q hnTen
  have hTaylor : |Real.exp (-μ) - ideal| ≤
      2 * (5 : ℝ) ^ m / (m.factorial : ℝ) := by
    simpa [ideal, poissonAlternatingTerm] using
      abs_exp_neg_sub_poissonPartial_le hμ0 hμ5 hmten
  have hActual : |actual - ideal| < ε / 4 := by
    simpa [actual, ideal] using hnBF P Q
  have hMeanCap : μ ≤ collisionMeanCap n := by
    exact collisionMean_le P Q (by omega)
  have hExpMono : Real.exp (-collisionMeanCap n) ≤ Real.exp (-μ) := by
    exact Real.exp_le_exp.mpr (neg_le_neg hMeanCap)
  have hActualLower : Real.exp (-(9 : ℝ) / 2) - ε < actual := by
    rw [abs_lt] at hActual
    rw [abs_le] at hTaylor
    linarith
  have hindex : m - 1 = 2 * r + 1 := by simp [m]
  have hBonferroni : actual ≤ normalizedZeroCount (collisionCount P Q) := by
    change normalizedBonferroni (collisionCount P Q) (m - 1) ≤
      normalizedZeroCount (collisionCount P Q)
    rw [hindex]
    exact oddBonferroni_le_normalizedZeroCount (collisionCount P Q) r
  exact hActualLower.le.trans hBonferroni

end Kourovka213
