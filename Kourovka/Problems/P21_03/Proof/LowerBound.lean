import Kourovka.Problems.P21_03.Proof.AsymptoticSqueeze
import Kourovka.Problems.P21_03.Proof.ConfigurationPoisson.ConfigurationLimit
import Kourovka.Problems.P21_03.Proof.CoreProbability
import Kourovka.Problems.P21_03.Proof.SupportError

/-!
# Assembly of the uniform lower bound

This module contains no asymptotic assumption about soluble groups.  It packages the
two quantitative inputs that remain to be proved elsewhere:

* a uniform lower error for the bounded configuration model;
* the uniform support estimates for soluble permutation groups.

The conclusion is the exact lower estimate for the infimum in Problem 21.3.
-/

open Filter
open scoped Topology

namespace Kourovka213

/-- A quantitative uniform lower bound for all block-size-at-most-four
configuration models in degree `n`. -/
def UniformConfigurationLowerBound (configurationError : ℕ → ℝ) : Prop :=
  ∀ (n : ℕ) (P Q : BoundedPartition n),
    Real.exp (-(9 : ℝ) / 2) - configurationError n ≤
      normalizedZeroCount (collisionCount P Q)

/-- It is enough to control one soluble forest envelope of each soluble subgroup.
The containment direction is chosen so that success probability is antitone. -/
def UniformSupportEnvelopeBounds (C : ℕ) : Prop :=
  ∀ (n : ℕ) (H : SolubleSubgroup n),
    ∃ M : SolubleSubgroup n, H.carrier ≤ M.carrier ∧ SupportBoundsFor C M

/-- The envelope estimate in the positive degrees relevant at `atTop`. -/
def PositiveSupportEnvelopeBounds (C : ℕ) : Prop :=
  ∀ (n : ℕ) (H : SolubleSubgroup n), 0 < n →
    ∃ M : SolubleSubgroup n, H.carrier ≤ M.carrier ∧ SupportBoundsFor C M

/-- Eventual uniform lower bound for the bounded configuration model. -/
def UniformConfigurationLowerAsymptotic : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
    ∀ P Q : BoundedPartition n,
      Real.exp (-(9 : ℝ) / 2) - ε ≤
        normalizedZeroCount (collisionCount P Q)

/-- The core probability is exactly the normalized zero-collision mass of the
two canonical bounded partitions. -/
theorem coreSuccessProbability_eq_normalizedZeroCount
    (H K : SolubleSubgroup n) :
    coreSuccessProbability H K =
      normalizedZeroCount
        (collisionCount (corePartition H.carrier) (corePartition K.carrier)) := by
  rfl

/-- Configuration-model and support-count errors add to a uniform lower bound
for every pair of soluble subgroups. -/
theorem successProbability_lower_bound_of_configuration_and_support
    {C : ℕ} {configurationError : ℕ → ℝ}
    (hconfiguration : UniformConfigurationLowerBound configurationError)
    (hsupport : UniformSupportBounds C)
    (H K : SolubleSubgroup n) :
    Real.exp (-(9 : ℝ) / 2) -
        (configurationError n + noncoreErrorBound C n) ≤
      successProbability H.carrier K.carrier := by
  rw [successProbability_eq_core_sub_extra,
    coreSuccessProbability_eq_normalizedZeroCount]
  have hcore := hconfiguration n (corePartition H.carrier) (corePartition K.carrier)
  have hextra := extraBadProbability_le_noncoreErrorBound_of_uniform hsupport H K
  linarith

/-- The preceding pointwise estimate descends to the infimum over soluble pairs. -/
theorem worstProbability_lower_bound_of_configuration_and_support
    {C : ℕ} {configurationError : ℕ → ℝ}
    (hconfiguration : UniformConfigurationLowerBound configurationError)
    (hsupport : UniformSupportBounds C) (n : ℕ) :
    Real.exp (-(9 : ℝ) / 2) -
        (configurationError n + noncoreErrorBound C n) ≤
      worstProbability n := by
  apply le_worstProbability_of_forall
  intro H K
  exact successProbability_lower_bound_of_configuration_and_support
    hconfiguration hsupport H K

/-- The lower estimate only needs pointwise support bounds for soluble overgroups
of the two subgroups under consideration. -/
theorem successProbability_lower_bound_of_envelopes
    {C : ℕ} {configurationError : ℕ → ℝ}
    (hconfiguration : UniformConfigurationLowerBound configurationError)
    {H K M N : SolubleSubgroup n}
    (hHM : H.carrier ≤ M.carrier) (hKN : K.carrier ≤ N.carrier)
    (hM : SupportBoundsFor C M) (hN : SupportBoundsFor C N) :
    Real.exp (-(9 : ℝ) / 2) -
        (configurationError n + noncoreErrorBound C n) ≤
      successProbability H.carrier K.carrier := by
  apply (show Real.exp (-(9 : ℝ) / 2) -
        (configurationError n + noncoreErrorBound C n) ≤
      successProbability M.carrier N.carrier by
    rw [successProbability_eq_core_sub_extra,
      coreSuccessProbability_eq_normalizedZeroCount]
    have hcore := hconfiguration n (corePartition M.carrier) (corePartition N.carrier)
    have hextra := extraBadProbability_le_noncoreErrorBound M N hM hN
    linarith).trans
  exact successProbability_antitone hHM hKN

/-- Forest envelopes give the uniform lower estimate for the infimum. -/
theorem worstProbability_lower_bound_of_envelopes
    {C : ℕ} {configurationError : ℕ → ℝ}
    (hconfiguration : UniformConfigurationLowerBound configurationError)
    (henvelopes : UniformSupportEnvelopeBounds C) (n : ℕ) :
    Real.exp (-(9 : ℝ) / 2) -
        (configurationError n + noncoreErrorBound C n) ≤
      worstProbability n := by
  apply le_worstProbability_of_forall
  intro H K
  obtain ⟨M, hHM, hM⟩ := henvelopes n H
  obtain ⟨N, hKN, hN⟩ := henvelopes n K
  exact successProbability_lower_bound_of_envelopes
    hconfiguration hHM hKN hM hN

/-- Once the configuration error tends to zero, the assembled lower error also
tends to zero. -/
theorem tendsto_totalLowerError_zero
    (C : ℕ) (configurationError : ℕ → ℝ)
    (hconfigurationError : Tendsto configurationError atTop (nhds 0)) :
    Tendsto (fun n ↦ configurationError n + noncoreErrorBound C n)
      atTop (nhds 0) := by
  convert hconfigurationError.add (tendsto_noncoreErrorBound_zero C) using 1 <;> simp

/-- Eventual configuration simplicity and forest-envelope support bounds imply
the matching eventual lower estimate for `worstProbability`. -/
theorem eventually_exp_sub_epsilon_le_worstProbability
    {C : ℕ} (hconfiguration : UniformConfigurationLowerAsymptotic)
    (henvelopes : PositiveSupportEnvelopeBounds C)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      Real.exp (-(9 : ℝ) / 2) - ε ≤ worstProbability n := by
  have hhalf : 0 < ε / 2 := half_pos hε
  have hnoncore : ∀ᶠ n : ℕ in atTop, noncoreErrorBound C n < ε / 2 := by
    have ht := tendsto_noncoreErrorBound_zero C
    exact ht.eventually (Iio_mem_nhds hhalf)
  filter_upwards [hconfiguration (ε / 2) hhalf, hnoncore,
    eventually_ge_atTop 1] with n hconfig hnerr hn
  have hnpos : 0 < n := by omega
  have hall : ∀ H K : SolubleSubgroup n,
      Real.exp (-(9 : ℝ) / 2) - ε <
        successProbability H.carrier K.carrier := by
    intro H K
    obtain ⟨M, hHM, hM⟩ := henvelopes n H hnpos
    obtain ⟨N, hKN, hN⟩ := henvelopes n K hnpos
    have hcore : Real.exp (-(9 : ℝ) / 2) - ε / 2 ≤
        coreSuccessProbability M N := by
      rw [coreSuccessProbability_eq_normalizedZeroCount]
      exact hconfig (corePartition M.carrier) (corePartition N.carrier)
    have hextra : extraBadProbability M N ≤ noncoreErrorBound C n :=
      extraBadProbability_le_noncoreErrorBound M N hM hN
    have hMN : Real.exp (-(9 : ℝ) / 2) - ε <
        successProbability M.carrier N.carrier := by
      rw [successProbability_eq_core_sub_extra]
      linarith
    exact hMN.trans_le (successProbability_antitone hHM hKN)
  exact le_worstProbability_of_forall n
    (Real.exp (-(9 : ℝ) / 2) - ε) (fun H K ↦ (hall H K).le)

/-- Final metric squeeze using the uniform lower theorem and one explicit
upper-witness sequence. -/
theorem asymptoticStatement_of_uniform_lower_and_witness
    {C : ℕ} (hconfiguration : UniformConfigurationLowerAsymptotic)
    (henvelopes : PositiveSupportEnvelopeBounds C)
    (witnessProbability : ℕ → ℝ)
    (hwitness : Tendsto witnessProbability atTop
      (nhds (Real.exp (-(9 : ℝ) / 2))))
    (hupper : ∀ n, worstProbability n ≤ witnessProbability n) :
    AsymptoticStatement := by
  rw [AsymptoticStatement, Metric.tendsto_atTop]
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  have hlower := eventually_exp_sub_epsilon_le_worstProbability
    hconfiguration henvelopes hhalf
  rw [eventually_atTop] at hlower
  obtain ⟨L, hL⟩ := hlower
  rw [Metric.tendsto_atTop] at hwitness
  obtain ⟨N, hN⟩ := hwitness (ε / 2) hhalf
  refine ⟨max L N, fun n hn ↦ ?_⟩
  have hnLower := hL n ((le_max_left L N).trans hn)
  have hn : N ≤ n := (le_max_right L N).trans hn
  have hnWitness := hN n hn
  rw [Real.dist_eq, abs_lt] at hnWitness ⊢
  constructor
  · linarith
  · linarith [hupper n, hnWitness.2]

end Kourovka213
