import Kourovka.Problems.P21_38.Statement
import Kourovka.Problems.P21_38.Proof.PrescribedGeneration
import Kourovka.Problems.P21_38.Proof.UpperBound
import Kourovka.Problems.P21_38.Proof.SpreadBounds

/-!
# An infinite group of ordinary spread exactly one

This answers Donoven and Harper's Question 2 in *Infinite 3/2-generated
groups* (2020), subsequently recorded as Kourovka Notebook Problem 21.38.
The witness is the concrete dyadic PL interval group with equal endpoint
exponents. Every mathematical dependency in the generation argument is
proved in the imported modules.
-/

namespace Kourovka.P21_38

/-- The equal-endpoint subgroup has ordinary spread exactly one. -/
theorem diagonal_hasSpreadExactlyOne : HasSpreadExactlyOne diagonalSubgroup :=
  ⟨diagonal_hasSpreadAtLeast_one, diagonal_not_hasSpreadAtLeast_two⟩

/-- The full tuple formulation: precisely the lengths zero and one work. -/
theorem diagonal_spread_profile (k : ℕ) :
    HasSpreadAtLeast diagonalSubgroup k ↔ k ≤ 1 :=
  (hasSpreadExactlyOne_iff_forall.mp diagonal_hasSpreadExactlyOne) k

/-- Affirmative answer to the original question of Donoven and Harper. -/
theorem originalQuestion : OriginalQuestion :=
  ⟨diagonalSubgroup, inferInstance, diagonal_infinite, diagonal_hasSpreadExactlyOne⟩

/-- Affirmative answer to Kourovka Notebook Problem 21.38. -/
theorem notebookStatement : NotebookStatement :=
  notebookStatement_of_originalQuestion originalQuestion

#audit_closed_axioms originalQuestion
#audit_closed_axioms notebookStatement
#audit_axioms diagonal_hasSpreadExactlyOne
#audit_axioms diagonal_spread_profile

end Kourovka.P21_38
