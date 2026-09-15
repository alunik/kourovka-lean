import Mathlib.Algebra.Group.Action.End
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.Torsion
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Problem 21.40

Dantas and de Melo ask whether a subgroup of `GL_n(ℚ)` with finitely many
orbits under its full abstract automorphism group is virtually soluble.
The question is recorded in the 21st edition of the Kourovka Notebook,
version 46 (1 September 2026), page 173. No finite-generation hypothesis
is imposed. We do not assert that the question first appeared there.
-/

namespace Kourovka.P21_40

/-- Finitely many orbits of the full abstract automorphism group on the group. -/
def HasFiniteAutomorphismOrbits (G : Type*) [Group G] : Prop :=
  Finite (MulAction.orbitRel.Quotient (MulAut G) G)

/-- A group is virtually soluble if it has a soluble subgroup of finite index. -/
def IsVirtuallySolvable (G : Type*) [Group G] : Prop :=
  ∃ K : Subgroup G, K.FiniteIndex ∧ Group.IsSolvable K

/-- The full question in Kourovka Notebook Problem 21.40, including dimension zero. -/
def NotebookStatement : Prop :=
  ∀ (n : ℕ) (G : Subgroup (Matrix.GeneralLinearGroup (Fin n) ℚ)),
    HasFiniteAutomorphismOrbits G → IsVirtuallySolvable G

/-- Upper unitriangular means diagonal entries one and entries below the diagonal zero. -/
def IsUpperUnitriangular {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) : Prop :=
  (∀ i, A i i = 1) ∧ ∀ i j, j < i → A i j = 0

/-- The quantitative structural strengthening of the Notebook question.

There is one normal finite-index subgroup and one rational change of basis
for all its elements. Finiteness of the index is explicit: the numerical
bound alone would not rule out mathlib's value zero for an infinite index.
-/
def StructuralConclusion {n : ℕ}
    (G : Subgroup (Matrix.GeneralLinearGroup (Fin n) ℚ)) : Prop :=
  ∃ K : Subgroup G, K.Normal ∧ K.FiniteIndex ∧
    K.index ≤ (2 * n + 1) ^ (n ^ 2) ∧
    Group.IsNilpotent K ∧ Group.nilpotencyClass K ≤ n - 1 ∧
    (∀ g : K, IsOfFinOrder g → g = 1) ∧
    ∃ P : Matrix.GeneralLinearGroup (Fin n) ℚ, ∀ g : G, g ∈ K →
      IsUpperUnitriangular
        ((P⁻¹ * (g : Matrix.GeneralLinearGroup (Fin n) ℚ) * P :
          Matrix.GeneralLinearGroup (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ)

end Kourovka.P21_40
