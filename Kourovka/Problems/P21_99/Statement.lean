import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Algebra.Group.Action.End
import Mathlib.Algebra.Group.Action.Pretransitive
import Mathlib.Data.Finite.Defs

/-! Peter Müller's Problem 21.99, in its finite permutation-action formulation. -/

namespace Kourovka.P21_99

/-- The question in the 21st Kourovka Notebook: every ordered pair of distinct
points admits a transporter whose number of fixed points is different from one.
The fixed-point condition is expressed as the negation of unique existence. -/
def NotebookStatement : Prop :=
  ∀ (Ω : Type) (G : Subgroup (Equiv.Perm Ω)),
    Finite Ω → MulAction.IsPretransitive G Ω →
      ∀ a b : Ω, a ≠ b →
        ∃ g : G, g • a = b ∧ ¬∃! x : Ω, g • x = x

end Kourovka.P21_99
