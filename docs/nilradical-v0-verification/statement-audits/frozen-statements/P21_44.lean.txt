import Kourovka.Problems.P21_44.Proof.InverseLimit
import Kourovka.Problems.P21_44.Proof.RecurrentSections.ExponentialGrowth
import Mathlib.GroupTheory.Finiteness

/-!
# Kourovka Notebook 21.44

Sean Eberhard asks whether the inverse limit of the iterated natural
degree-five alternating wreath products contains a finitely generated
dense subgroup of subexponential growth.

`AutTree` is that actual inverse limit, with the topology inherited from
the product of its discrete finite levels. Word balls are ordinary products
of a finite symmetric generating set containing the identity. The growth
condition is the limit `log |B(n)| / n → 0`.
-/

namespace Kourovka.P21_44

/-- Ordinary subexponential growth, witnessed by a finite symmetric
generating set and its usual word balls. -/
def HasSubexponentialGrowth (G : Type*) [Group G] : Prop := by
  classical
  exact ∃ V : RecurrentSections.WordGeometry G,
    RecurrentSections.SubexponentialGrowth V.volume

/-- The question's ambient group and topology are fixed; only its abstract
finitely generated dense subgroup is existentially quantified. -/
def NotebookStatement : Prop :=
  ∃ H : Subgroup AutTree, H.FG ∧ Dense (H : Set AutTree) ∧ HasSubexponentialGrowth H

end Kourovka.P21_44
