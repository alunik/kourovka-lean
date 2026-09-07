import Kourovka.Problems.P21_03.Proof.Bonferroni
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# A binomial-moment criterion for Poisson zero mass

This file packages the analytic half of the Brun sieve used for the bounded
configuration model.  It is deliberately independent of collision witnesses:
for finite, nonempty probability spaces, convergence of every normalized
binomial moment to `lambda ^ j / j!` forces the mass at zero to converge to
`exp (-lambda)`.
-/

open scoped BigOperators Topology
open Filter

namespace Kourovka213

section Finite

variable {Omega : Type*} [Fintype Omega]

/-- Uniform probability that a natural-valued statistic vanishes. -/
noncomputable def normalizedZeroCount [Nonempty Omega] (Z : Omega → ℕ) : ℝ :=
  zeroCount Z / Fintype.card Omega

/-- Uniformly normalized binomial moment. -/
noncomputable def normalizedBinomialMoment [Nonempty Omega]
    (Z : Omega → ℕ) (j : ℕ) : ℝ :=
  binomialMoment Z j / Fintype.card Omega

/-- The real-valued Bonferroni polynomial made from normalized moments. -/
noncomputable def normalizedBonferroni [Nonempty Omega]
    (Z : Omega → ℕ) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (k + 1), (-1 : ℝ) ^ j * normalizedBinomialMoment Z j

theorem normalizedZeroCount_le_evenBonferroni [Nonempty Omega]
    (Z : Omega → ℕ) (r : ℕ) :
    normalizedZeroCount Z ≤ normalizedBonferroni Z (2 * r) := by
  have hcard : (0 : ℝ) < Fintype.card Omega := by
    exact_mod_cast Fintype.card_pos
  unfold normalizedZeroCount normalizedBonferroni normalizedBinomialMoment
  simp_rw [← mul_div_assoc]
  rw [← Finset.sum_div]
  apply (div_le_div_iff_of_pos_right hcard).2
  have h := zeroCount_le_evenBonferroni Z r
  push_cast
  exact_mod_cast h

theorem oddBonferroni_le_normalizedZeroCount [Nonempty Omega]
    (Z : Omega → ℕ) (r : ℕ) :
    normalizedBonferroni Z (2 * r + 1) ≤ normalizedZeroCount Z := by
  have hcard : (0 : ℝ) < Fintype.card Omega := by
    exact_mod_cast Fintype.card_pos
  unfold normalizedZeroCount normalizedBonferroni normalizedBinomialMoment
  simp_rw [← mul_div_assoc]
  rw [← Finset.sum_div]
  apply (div_le_div_iff_of_pos_right hcard).2
  have h := oddBonferroni_le_zeroCount Z r
  push_cast
  exact_mod_cast h

end Finite

/-- The limiting summand in the Poisson inclusion--exclusion series. -/
noncomputable def poissonAlternatingTerm (lambda : ℝ) (j : ℕ) : ℝ :=
  (-lambda) ^ j / j.factorial

theorem hasSum_poissonAlternatingTerm (lambda : ℝ) :
    HasSum (poissonAlternatingTerm lambda) (Real.exp (-lambda)) := by
  rw [Real.exp_eq_exp_ℝ]
  change HasSum (fun j : ℕ => (-lambda) ^ j / (j.factorial : ℝ))
    (NormedSpace.exp (-lambda))
  exact NormedSpace.expSeries_div_hasSum_exp (-lambda : ℝ)

theorem tendsto_poissonAlternatingPartialSum (lambda : ℝ) :
    Tendsto (fun k : ℕ => ∑ j ∈ Finset.range (k + 1), poissonAlternatingTerm lambda j)
      atTop (nhds (Real.exp (-lambda))) := by
  rw [tendsto_add_atTop_iff_nat
    (f := fun k : ℕ => ∑ j ∈ Finset.range k, poissonAlternatingTerm lambda j) 1]
  exact (hasSum_poissonAlternatingTerm lambda).tendsto_sum_nat

section Criterion

variable (Omega : ℕ → Type*) [∀ n, Fintype (Omega n)] [∀ n, Nonempty (Omega n)]

private theorem tendsto_normalizedBonferroni_of_moments
    (Z : ∀ n, Omega n → ℕ) (lambda : ℝ)
    (hmoment : ∀ j : ℕ,
      Tendsto (fun n => normalizedBinomialMoment (Z n) j) atTop
        (nhds (lambda ^ j / (j.factorial : ℝ)))) (k : ℕ) :
    Tendsto (fun n => normalizedBonferroni (Z n) k) atTop
      (nhds (∑ j ∈ Finset.range (k + 1), poissonAlternatingTerm lambda j)) := by
  unfold normalizedBonferroni
  apply tendsto_finsetSum
  intro j _hj
  convert tendsto_const_nhds.mul (hmoment j) using 1
  unfold poissonAlternatingTerm
  rw [neg_pow]
  ring

/-- **Brun's binomial-moment criterion.**  On a sequence of nonempty finite
uniform spaces, convergence of every binomial moment to the corresponding
Poisson binomial moment implies convergence of the zero mass.

This is the exact analytic interface needed by the configuration-model count:
the model-specific argument only has to prove `hmoment`. -/
theorem tendsto_normalizedZeroCount_of_binomialMoments
    (Z : ∀ n, Omega n → ℕ) (lambda : ℝ)
    (hmoment : ∀ j : ℕ,
      Tendsto (fun n => normalizedBinomialMoment (Z n) j) atTop
        (nhds (lambda ^ j / (j.factorial : ℝ)))) :
    Tendsto (fun n => normalizedZeroCount (Z n)) atTop
      (nhds (Real.exp (-lambda))) := by
  refine Metric.tendsto_atTop.mpr fun epsilon hepsilon => ?_
  have hseries := tendsto_poissonAlternatingPartialSum lambda
  rw [Metric.tendsto_atTop] at hseries
  obtain ⟨r, hr⟩ := hseries (epsilon / 2) (half_pos hepsilon)
  let lowerIndex := 2 * r + 1
  let upperIndex := 2 * r
  have hrLower : r ≤ lowerIndex := by simp [lowerIndex]; omega
  have hrUpper : r ≤ upperIndex := by simp [upperIndex]; omega
  have hlowerSeries := hr lowerIndex hrLower
  have hupperSeries := hr upperIndex hrUpper
  have hlower := tendsto_normalizedBonferroni_of_moments Omega Z lambda hmoment lowerIndex
  have hupper := tendsto_normalizedBonferroni_of_moments Omega Z lambda hmoment upperIndex
  rw [Metric.tendsto_atTop] at hlower hupper
  obtain ⟨nLower, hnLower⟩ := hlower (epsilon / 2) (half_pos hepsilon)
  obtain ⟨nUpper, hnUpper⟩ := hupper (epsilon / 2) (half_pos hepsilon)
  refine ⟨max nLower nUpper, fun n hn => ?_⟩
  have hnL : nLower ≤ n := (le_max_left _ _).trans hn
  have hnU : nUpper ≤ n := (le_max_right _ _).trans hn
  have hdistLower :
      dist (normalizedBonferroni (Z n) lowerIndex) (Real.exp (-lambda)) < epsilon :=
    calc
      dist (normalizedBonferroni (Z n) lowerIndex) (Real.exp (-lambda)) ≤
          dist (normalizedBonferroni (Z n) lowerIndex)
              (∑ j ∈ Finset.range (lowerIndex + 1), poissonAlternatingTerm lambda j) +
            dist (∑ j ∈ Finset.range (lowerIndex + 1), poissonAlternatingTerm lambda j)
              (Real.exp (-lambda)) := dist_triangle _ _ _
      _ < epsilon / 2 + epsilon / 2 := add_lt_add (hnLower n hnL) hlowerSeries
      _ = epsilon := by ring
  have hdistUpper :
      dist (normalizedBonferroni (Z n) upperIndex) (Real.exp (-lambda)) < epsilon :=
    calc
      dist (normalizedBonferroni (Z n) upperIndex) (Real.exp (-lambda)) ≤
          dist (normalizedBonferroni (Z n) upperIndex)
              (∑ j ∈ Finset.range (upperIndex + 1), poissonAlternatingTerm lambda j) +
            dist (∑ j ∈ Finset.range (upperIndex + 1), poissonAlternatingTerm lambda j)
              (Real.exp (-lambda)) := dist_triangle _ _ _
      _ < epsilon / 2 + epsilon / 2 := add_lt_add (hnUpper n hnU) hupperSeries
      _ = epsilon := by ring
  have hlowerLe : normalizedBonferroni (Z n) lowerIndex ≤ normalizedZeroCount (Z n) := by
    simpa [lowerIndex] using oddBonferroni_le_normalizedZeroCount (Z n) r
  have hleUpper : normalizedZeroCount (Z n) ≤ normalizedBonferroni (Z n) upperIndex := by
    simpa [upperIndex] using normalizedZeroCount_le_evenBonferroni (Z n) r
  rw [Real.dist_eq] at hdistLower hdistUpper ⊢
  rw [abs_lt] at hdistLower hdistUpper ⊢
  constructor <;> linarith

end Criterion

end Kourovka213
