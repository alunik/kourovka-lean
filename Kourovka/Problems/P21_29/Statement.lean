import Mathlib.GroupTheory.GroupAction.Primitive
import Mathlib.GroupTheory.GroupAction.Defs

/-! Problem 21.29, expressed using two-point stabilizers. -/

namespace Kourovka.P21_29

/-- The intersection of the two point stabilizers is the identity subgroup. -/
def TrivialPairStabilizer {Ω : Type*} (G : Subgroup (Equiv.Perm Ω)) (a b : Ω) : Prop :=
  MulAction.stabilizer G a ⊓ MulAction.stabilizer G b = ⊥

/-- The question of Burness and Giudici in the 21st Kourovka Notebook. -/
def NotebookStatement : Prop :=
  ∀ (Ω : Type) (G : Subgroup (Equiv.Perm Ω)),
    Finite G → MulAction.IsPreprimitive G Ω →
    (∃ a b : Ω, TrivialPairStabilizer G a b) →
      ∀ a b : Ω, ∃ c : Ω,
        TrivialPairStabilizer G a c ∧ TrivialPairStabilizer G b c

end Kourovka.P21_29
