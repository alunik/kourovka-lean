import Kourovka.Problems.P21_03.Proof.Bonferroni
import Kourovka.Problems.P21_03.Proof.CorePartition

/-!
# Separating the transposition-core event

The asymptotic proof first analyzes the two bounded Young subgroups carried by the
transposition cores.  This file records the exact finite identity separating that event
from the error caused by elements outside a core.
-/

namespace Kourovka213

open scoped Pointwise

variable {n : ℕ}

/-- Exact probability that the two canonical core partitions have no collision. -/
noncomputable def coreSuccessProbability (H K : SolubleSubgroup n) : ℝ :=
  (zeroCount fun sigma : Sym n =>
      collisionCount (corePartition H.carrier) (corePartition K.carrier) sigma) /
    Fintype.card (Sym n)

/-- Conjugators for which the cores are disjoint but the original subgroups are not. -/
noncomputable def extraBadConjugators (H K : SolubleSubgroup n) : Finset (Sym n) := by
  classical
  exact Finset.univ.filter fun sigma =>
    Disjoint (transpositionCore H.carrier)
        (conjugate (transpositionCore K.carrier) sigma) ∧
      ¬ Disjoint H.carrier (conjugate K.carrier sigma)

/-- Uniform mass of the non-core error event. -/
noncomputable def extraBadProbability (H K : SolubleSubgroup n) : ℝ :=
  (extraBadConjugators H K).card / Fintype.card (Sym n)

private theorem conjugate_transpositionCore_le (K : Subgroup (Sym n)) (sigma : Sym n) :
    conjugate (transpositionCore K) sigma ≤ conjugate K sigma := by
  exact smul_le_smul_left (MulAut.conj sigma⁻¹) (transpositionCore_le K)

private theorem full_disjoint_implies_core_disjoint
    (H K : Subgroup (Sym n)) (sigma : Sym n)
    (h : Disjoint H (conjugate K sigma)) :
    Disjoint (transpositionCore H) (conjugate (transpositionCore K) sigma) :=
  Disjoint.mono (transpositionCore_le H) (conjugate_transpositionCore_le K sigma) h

/-- The collision-model probability is literally the success probability of the two
transposition cores. -/
theorem coreSuccessProbability_eq (H K : SolubleSubgroup n) :
    coreSuccessProbability H K =
      successProbability (transpositionCore H.carrier) (transpositionCore K.carrier) := by
  classical
  have hfin :
      Finset.univ.filter (fun sigma : Sym n =>
        collisionCount (corePartition H.carrier) (corePartition K.carrier) sigma = 0) =
      goodConjugators (transpositionCore H.carrier) (transpositionCore K.carrier) := by
    ext sigma
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_goodConjugators]
    rw [← disjoint_transpositionCore_conjugate_iff_collisionCount_eq_zero]
  simpa [coreSuccessProbability, successProbability, zeroCount] using
    congrArg (fun s : Finset (Sym n) =>
      (s.card : ℝ) / Fintype.card (Sym n)) hfin

private theorem card_core_good_eq_add_extra (H K : SolubleSubgroup n) :
    (goodConjugators (transpositionCore H.carrier)
        (transpositionCore K.carrier)).card =
      (goodConjugators H.carrier K.carrier).card +
        (extraBadConjugators H K).card := by
  classical
  let coreGood := goodConjugators (transpositionCore H.carrier)
    (transpositionCore K.carrier)
  let fullGood : Sym n → Prop := fun sigma =>
    Disjoint H.carrier (conjugate K.carrier sigma)
  have hsplit := Finset.card_filter_add_card_filter_not (s := coreGood) fullGood
  have hfirst : coreGood.filter fullGood = goodConjugators H.carrier K.carrier := by
    ext sigma
    simp only [coreGood, fullGood, Finset.mem_filter, mem_goodConjugators]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨full_disjoint_implies_core_disjoint H.carrier K.carrier sigma h, h⟩
  have hsecond : coreGood.filter (fun sigma => ¬ fullGood sigma) =
      extraBadConjugators H K := by
    ext sigma
    simp [coreGood, fullGood, extraBadConjugators]
  rw [hfirst, hsecond] at hsplit
  simpa [coreGood] using hsplit.symm

/-- Exact decomposition: core simplicity equals genuine success plus the non-core error. -/
theorem coreSuccessProbability_eq_add_extra (H K : SolubleSubgroup n) :
    coreSuccessProbability H K =
      successProbability H.carrier K.carrier + extraBadProbability H K := by
  rw [coreSuccessProbability_eq, successProbability, extraBadProbability,
    card_core_good_eq_add_extra]
  push_cast
  exact add_div _ _ _

theorem successProbability_eq_core_sub_extra (H K : SolubleSubgroup n) :
    successProbability H.carrier K.carrier =
      coreSuccessProbability H K - extraBadProbability H K := by
  rw [coreSuccessProbability_eq_add_extra]
  ring

theorem successProbability_le_coreSuccessProbability (H K : SolubleSubgroup n) :
    successProbability H.carrier K.carrier ≤ coreSuccessProbability H K := by
  rw [coreSuccessProbability_eq_add_extra]
  exact le_add_of_nonneg_right (div_nonneg (by positivity) (by positivity))

end Kourovka213
