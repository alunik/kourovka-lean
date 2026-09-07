import Kourovka.Problems.P21_03.Proof.ForestEnvelopeBounds
import Mathlib.Order.Preorder.Finite

/-!
# Reduction to maximal soluble forest envelopes

Because the ambient symmetric group is finite, every soluble subgroup is
contained in a maximal soluble subgroup.  Maximality then forces the full
forest envelope supplied by the structural theorem to equal the subgroup
itself.  This removes the enlargement caveat from all subsequent portrait
counts.
-/

namespace Kourovka213

open scoped Pointwise

variable {n : ℕ}

/-- Maximality among soluble subgroups of the same symmetric group. -/
def IsMaximalSoluble (M : SolubleSubgroup n) : Prop :=
  ∀ N : SolubleSubgroup n, M.carrier ≤ N.carrier → N.carrier = M.carrier

/-- Every soluble permutation subgroup has a maximal soluble overgroup. -/
theorem exists_maximalSoluble_overgroup (H : SolubleSubgroup n) :
    ∃ M : SolubleSubgroup n,
      H.carrier ≤ M.carrier ∧ IsMaximalSoluble M := by
  let good : Subgroup (Sym n) → Prop := fun M ↦ Group.IsSolvable M
  obtain ⟨M, hHM, hmax⟩ :=
    Finite.exists_le_maximal (p := good) (a := H.carrier) H.isSolvable
  let Msol : SolubleSubgroup n :=
    { carrier := M
      isSolvable := hmax.1 }
  refine ⟨Msol, hHM, ?_⟩
  intro N hMN
  exact (hmax.2 N.isSolvable hMN).antisymm hMN

/-- A maximal soluble subgroup is exactly its transported full forest
envelope. -/
theorem forestEnvelope_eq_of_isMaximalSoluble
    (M : SolubleSubgroup n) (hM : IsMaximalSoluble M) (hn : 0 < n) :
    (M.forestEnvelope hn).carrier = M.carrier :=
  hM (M.forestEnvelope hn) (M.le_forestEnvelope hn)

/-- Packaged equality of soluble subgroups. -/
theorem forestEnvelope_eq_of_isMaximalSoluble'
    (M : SolubleSubgroup n) (hM : IsMaximalSoluble M) (hn : 0 < n) :
    M.forestEnvelope hn = M := by
  apply SolubleSubgroup.ext
  exact forestEnvelope_eq_of_isMaximalSoluble M hM hn

/-- It is enough to prove existence for maximal soluble overgroups. -/
theorem exists_goodConjugator_of_maximal_overgroups
    (H K M N : SolubleSubgroup n)
    (hHM : H.carrier ≤ M.carrier) (hKN : K.carrier ≤ N.carrier)
    (hgood : ∃ sigma : Sym n,
      Disjoint M.carrier (conjugate N.carrier sigma)) :
    ∃ sigma : Sym n, Disjoint H.carrier (conjugate K.carrier sigma) := by
  obtain ⟨sigma, hsigma⟩ := hgood
  exact ⟨sigma, Disjoint.mono hHM
    (smul_le_smul_left (MulAut.conj sigma⁻¹) hKN) hsigma⟩

/-- Probability form of the same maximal-overgroup reduction. -/
theorem maximal_overgroup_successProbability_le
    (H K M N : SolubleSubgroup n)
    (hHM : H.carrier ≤ M.carrier) (hKN : K.carrier ≤ N.carrier) :
    successProbability M.carrier N.carrier ≤
      successProbability H.carrier K.carrier :=
  successProbability_antitone hHM hKN

/-- A convenient all-pairs reduction: a theorem for every maximal soluble
pair implies the desired existence statement for every soluble pair. -/
theorem all_soluble_of_all_maximalSoluble
    (hmax : ∀ M N : SolubleSubgroup n,
      IsMaximalSoluble M → IsMaximalSoluble N →
        ∃ sigma : Sym n, Disjoint M.carrier (conjugate N.carrier sigma)) :
    ∀ H K : SolubleSubgroup n,
      ∃ sigma : Sym n, Disjoint H.carrier (conjugate K.carrier sigma) := by
  intro H K
  obtain ⟨M, hHM, hMmax⟩ := exists_maximalSoluble_overgroup H
  obtain ⟨N, hKN, hNmax⟩ := exists_maximalSoluble_overgroup K
  exact exists_goodConjugator_of_maximal_overgroups H K M N hHM hKN
    (hmax M N hMmax hNmax)

end Kourovka213
