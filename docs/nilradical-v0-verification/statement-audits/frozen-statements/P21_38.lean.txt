import Kourovka.Problems.P21_38.Proof.Spread

/-!
# The question of Donoven and Harper

The original Question 2 in *Infinite 3/2-generated groups* (2020) asks for an
infinite group of spread one. Kourovka Notebook Problem 21.38 asks whether a
group of spread one exists. These are only the statements; no existence proof
is declared in this module.
-/

namespace Kourovka.P21_38

/-- The question in Donoven and Harper's original paper. -/
def OriginalQuestion : Prop :=
  ∃ (G : Type) (group : Group G), Infinite G ∧ @HasSpreadExactlyOne G group

/-- The unrestricted question recorded as Kourovka Notebook Problem 21.38. -/
def NotebookStatement : Prop :=
  ∃ (G : Type) (group : Group G), @HasSpreadExactlyOne G group

/-- An answer to the original question answers the Notebook question. -/
theorem notebookStatement_of_originalQuestion (h : OriginalQuestion) : NotebookStatement := by
  obtain ⟨G, group, _, hG⟩ := h
  exact ⟨G, group, hG⟩

end Kourovka.P21_38
