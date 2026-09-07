import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.Solvable
import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Problem 21.3, first question

M. Anagnostopoulou-Merkouri and T. C. Burness, Kourovka Notebook,
21st edition, p. 167. For all sufficiently large `n`, do any two soluble
subgroups of `S_n` (respectively `A_n`) have disjoint conjugates?

We represent subgroups of `A_n` as subgroups of `S_n` contained in `A_n`.
The alternating conclusion explicitly requires the conjugator to be even.
Conjugation is `K ↦ x⁻¹ K x`; `Disjoint` means intersection equal to `⊥`.
The cutoff is uniform over both groups and all pairs of soluble subgroups.
-/

open scoped Pointwise

namespace Kourovka.P21_03

/-- The first question of Problem 21.3, with an affirmative answer. -/
def FirstQuestion : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    (∀ H K : Subgroup (Equiv.Perm (Fin n)),
      Group.IsSolvable H → Group.IsSolvable K →
        ∃ x : Equiv.Perm (Fin n), Disjoint H (MulAut.conj x⁻¹ • K)) ∧
    (∀ H K : Subgroup (Equiv.Perm (Fin n)),
      Group.IsSolvable H → Group.IsSolvable K →
      H ≤ alternatingGroup (Fin n) → K ≤ alternatingGroup (Fin n) →
        ∃ x : Equiv.Perm (Fin n), x ∈ alternatingGroup (Fin n) ∧
          Disjoint H (MulAut.conj x⁻¹ • K))

end Kourovka.P21_03
