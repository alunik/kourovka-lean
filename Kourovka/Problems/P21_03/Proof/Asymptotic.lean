import Kourovka.Problems.P21_03.Proof.ForestEnvelopeBounds
import Kourovka.Problems.P21_03.Proof.UniformBrunLower
import Kourovka.Problems.P21_03.Proof.UpperWitness

/-!
# Solution of Kourovka Notebook Problem 21.3

The uniform forest-envelope lower bound and the soluble four-block upper
witness have the same limiting success probability.
-/

namespace Kourovka213

/-- The infimum, over pairs of soluble subgroups of `S_n`, of the probability
that a uniformly random conjugate has trivial intersection tends to
`exp (-9 / 2)`. -/
theorem asymptoticStatement : AsymptoticStatement :=
  asymptoticStatement_of_uniform_lower_and_witness
    (uniformConfigurationLowerAsymptotic_of_moments
      uniformCollisionMomentApproximation)
    positiveSupportEnvelopeBounds
    (fun n =>
      successProbability (fourBlockSolubleSubgroup n).carrier
        (fourBlockSolubleSubgroup n).carrier)
    (by
      simpa only [neg_div] using tendsto_fourBlockSuccessProbability)
    (fun n =>
      worstProbability_le_successProbability
        (fourBlockSolubleSubgroup n)
        (fourBlockSolubleSubgroup n))

end Kourovka213
