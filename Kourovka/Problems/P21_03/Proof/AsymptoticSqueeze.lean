import Kourovka.Problems.P21_03.Proof.Basic
import Mathlib.Topology.Algebra.Order.Field

/-!
# Final order-theoretic squeeze

This file isolates the last, purely analytic step of the proof.  The two inputs expected
from the group/configuration part are a uniform lower error and one explicit family giving
the matching upper error.
-/

open Filter
open scoped Topology

namespace Kourovka213

/-- A uniform lower bound for every soluble pair descends to the infimum defining
`worstProbability`. -/
theorem le_worstProbability_of_forall (n : ℕ) (a : ℝ)
    (h : ∀ H K : SolubleSubgroup n,
      a ≤ successProbability H.carrier K.carrier) :
    a ≤ worstProbability n := by
  rw [worstProbability]
  refine le_csInf (solubleProbabilities_nonempty n) ?_
  rintro p ⟨H, K, rfl⟩
  exact h H K

/-- Matching error bounds tending to zero imply the required limit. -/
theorem tendsto_worstProbability_of_error_bounds
    (c : ℝ) (lowerError upperError : ℕ → ℝ)
    (hlowerError : Tendsto lowerError atTop (nhds 0))
    (hupperError : Tendsto upperError atTop (nhds 0))
    (hlower : ∀ n, c - lowerError n ≤ worstProbability n)
    (hupper : ∀ n, worstProbability n ≤ c + upperError n) :
    Tendsto worstProbability atTop (nhds c) := by
  have hleft : Tendsto (fun n => c - lowerError n) atTop (nhds (c - 0)) :=
    tendsto_const_nhds.sub hlowerError
  have hright : Tendsto (fun n => c + upperError n) atTop (nhds (c + 0)) :=
    tendsto_const_nhds.add hupperError
  have hleft' : Tendsto (fun n => c - lowerError n) atTop (nhds c) := by
    simpa using hleft
  have hright' : Tendsto (fun n => c + upperError n) atTop (nhds c) := by
    simpa using hright
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hleft' hright' hlower hupper

/-- Specialized final gate for Problem 21.3. -/
theorem asymptoticStatement_of_error_bounds
    (lowerError upperError : ℕ → ℝ)
    (hlowerError : Tendsto lowerError atTop (nhds 0))
    (hupperError : Tendsto upperError atTop (nhds 0))
    (hlower : ∀ n,
      Real.exp (-(9 : ℝ) / 2) - lowerError n ≤ worstProbability n)
    (hupper : ∀ n,
      worstProbability n ≤ Real.exp (-(9 : ℝ) / 2) + upperError n) :
    AsymptoticStatement :=
  tendsto_worstProbability_of_error_bounds _ _ _ hlowerError hupperError hlower hupper

end Kourovka213
