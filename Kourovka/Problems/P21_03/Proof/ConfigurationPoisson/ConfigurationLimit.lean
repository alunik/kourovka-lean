import Kourovka.Problems.P21_03.Proof.ConfigurationPoisson.DisjointFamilies
import Kourovka.Problems.P21_03.Proof.ConfigurationPoisson.MomentCriterion

/-!
# The Poisson criterion specialized to bounded Young configurations
-/

open scoped Topology
open Filter

namespace Kourovka213

/-- Fraction of permutations producing a simple incidence table. -/
noncomputable def simpleConfigurationFraction (P Q : BoundedPartition n) : ℝ :=
  by
    classical
    exact (Finset.univ.filter fun sigma : Sym n => IsSimple P Q sigma).card /
      Fintype.card (Sym n)

theorem simpleConfigurationFraction_eq_normalizedZeroCount
    (P Q : BoundedPartition n) :
    simpleConfigurationFraction P Q =
      normalizedZeroCount (collisionCount P Q) := by
  classical
  unfold simpleConfigurationFraction normalizedZeroCount zeroCount
  have hfilter :
      (Finset.univ.filter fun sigma : Sym n => IsSimple P Q sigma) =
        Finset.univ.filter fun sigma : Sym n => collisionCount P Q sigma = 0 := by
    ext sigma
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact isSimple_iff_collisionCount_eq_zero P Q sigma
  rw [hfilter]

/-- The normalized first binomial moment is the previously computed collision
mean. -/
theorem normalizedBinomialMoment_one_eq_collisionMean
    (P Q : BoundedPartition n) :
    normalizedBinomialMoment (collisionCount P Q) 1 = collisionMean P Q := by
  classical
  unfold normalizedBinomialMoment binomialMoment collisionMean
    collisionFirstMomentNat
  norm_num

/-- Specialized Brun criterion for a sequence of bounded Young configurations.
The remaining model-specific obligation is precisely the convergence of all
collision binomial moments. -/
theorem tendsto_simpleConfigurationFraction_of_binomialMoments
    (P Q : ∀ n, BoundedPartition n) (lambda : ℝ)
    (hmoment : ∀ j : ℕ,
      Tendsto
        (fun n => normalizedBinomialMoment (collisionCount (P n) (Q n)) j)
        atTop (nhds (lambda ^ j / (j.factorial : ℝ)))) :
    Tendsto (fun n => simpleConfigurationFraction (P n) (Q n)) atTop
      (nhds (Real.exp (-lambda))) := by
  simp_rw [simpleConfigurationFraction_eq_normalizedZeroCount]
  exact tendsto_normalizedZeroCount_of_binomialMoments
    (fun n => Sym n) (fun n => collisionCount (P n) (Q n)) lambda hmoment

end Kourovka213
