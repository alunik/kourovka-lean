import Kourovka.Problems.P21_106.Statement
import Kourovka.Problems.P21_106.Proof.Counterexample

/-!
# A negative answer to Kourovka problem 21.106

The parameter-free formula `counterexampleFormula` has exactly two values in
the residually finite integral Heisenberg group. These values generate an
infinite subgroup. The formula is an actual first-order syntax object, and its
interpretation is linked to the semantic counterexample by a realization lemma.
-/

namespace Kourovka.P21_106

/-- The first-order value set is the set characterized by the algebraic proof. -/
theorem counterexample_values :
    FormulaValues counterexampleFormula H = {x : H | FormulaCondition x} := by
  ext x
  exact realize_counterexampleFormula x

/-- The exhibited parameter-free first-order formula is not concise in `H`. -/
theorem counterexample_not_concise : ¬ IsConciseIn counterexampleFormula H := by
  intro h
  have hfinite : (FormulaValues counterexampleFormula H).Finite := by
    rw [counterexample_values]
    exact formulaCondition_finite
  have hclosure := h hfinite
  rw [counterexample_values] at hclosure
  let := formulaCondition_closure_infinite
  exact not_finite (Subgroup.closure {x : H | FormulaCondition x})

/-- The universal conciseness assertion in Kourovka problem 21.106 is false. -/
theorem not_notebookStatement : ¬ NotebookStatement := fun h =>
  counterexample_not_concise (h H counterexampleFormula)

end Kourovka.P21_106
