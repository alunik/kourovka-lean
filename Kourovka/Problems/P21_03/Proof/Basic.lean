import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.GroupTheory.Perm.Centralizer
import Mathlib.GroupTheory.Solvable
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

/-!
# Kourovka Notebook 21.3: formal statement

This file fixes the exact finite probability and the asymptotic target.  Probabilities are
cardinality ratios, so the group-theoretic part of the development does not depend on a
measure-theory encoding of the uniform distribution.
-/

open Filter
open scoped Pointwise Topology

namespace Kourovka213

/-- The symmetric group of degree `n`. -/
abbrev Sym (n : ℕ) := Equiv.Perm (Fin n)

/-- A subgroup of `S_n`, packaged with a proof of solubility. -/
structure SolubleSubgroup (n : ℕ) where
  carrier : Subgroup (Sym n)
  isSolvable : Group.IsSolvable carrier

namespace SolubleSubgroup

instance (n : ℕ) : Coe (SolubleSubgroup n) (Subgroup (Sym n)) := ⟨carrier⟩

instance (H : SolubleSubgroup n) : Group.IsSolvable H.carrier := H.isSolvable

@[ext]
theorem ext {H K : SolubleSubgroup n} (h : H.carrier = K.carrier) : H = K := by
  cases H
  cases K
  cases h
  rfl

/-- The trivial subgroup is a soluble subgroup. -/
def bot (n : ℕ) : SolubleSubgroup n where
  carrier := ⊥
  isSolvable := inferInstance

end SolubleSubgroup

/-- Conjugation convention: `conjugate K x = x⁻¹ K x`. -/
def conjugate {n : ℕ} (K : Subgroup (Sym n)) (x : Sym n) : Subgroup (Sym n) :=
  MulAut.conj x⁻¹ • K

/-- The set of conjugators for which the two subgroups intersect trivially. -/
noncomputable def goodConjugators {n : ℕ} (H K : Subgroup (Sym n)) : Finset (Sym n) := by
  classical
  exact Finset.univ.filter fun x => Disjoint H (conjugate K x)

/-- Uniform probability that `H ∩ K^x` is trivial, written as an exact cardinal ratio. -/
noncomputable def successProbability {n : ℕ} (H K : Subgroup (Sym n)) : ℝ :=
  (goodConjugators H K).card / Fintype.card (Sym n)

@[simp]
theorem mem_goodConjugators {n : ℕ} {H K : Subgroup (Sym n)} {x : Sym n} :
    x ∈ goodConjugators H K ↔ Disjoint H (conjugate K x) := by
  classical
  simp [goodConjugators]

@[simp]
theorem card_sym (n : ℕ) : Fintype.card (Sym n) = n.factorial := by
  rw [Fintype.card_perm, Fintype.card_fin]

theorem successProbability_nonneg {n : ℕ} (H K : Subgroup (Sym n)) :
    0 ≤ successProbability H K := by
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem successProbability_le_one {n : ℕ} (H K : Subgroup (Sym n)) :
    successProbability H K ≤ 1 := by
  rw [successProbability, div_le_one₀]
  · exact_mod_cast Finset.card_le_card (Finset.subset_univ (goodConjugators H K))
  · exact_mod_cast Fintype.card_pos

/-- Enlarging either subgroup can only decrease the probability of a trivial
intersection. -/
theorem successProbability_antitone
    {H H' K K' : Subgroup (Sym n)} (hH : H ≤ H') (hK : K ≤ K') :
    successProbability H' K' ≤ successProbability H K := by
  classical
  unfold successProbability
  apply div_le_div_of_nonneg_right
  · exact_mod_cast Finset.card_le_card (show goodConjugators H' K' ⊆
        goodConjugators H K by
      intro sigma hsigma
      rw [mem_goodConjugators] at hsigma ⊢
      exact Disjoint.mono hH
        (smul_le_smul_left (MulAut.conj sigma⁻¹) hK) hsigma)
  · positivity

/-- The set of success probabilities arising from pairs of soluble subgroups of `S_n`. -/
def solubleProbabilities (n : ℕ) : Set ℝ :=
  {p | ∃ H K : SolubleSubgroup n,
    p = successProbability H.carrier K.carrier}

/-- The worst success probability in degree `n`. -/
noncomputable def worstProbability (n : ℕ) : ℝ :=
  sInf (solubleProbabilities n)

theorem solubleProbabilities_nonempty (n : ℕ) : (solubleProbabilities n).Nonempty := by
  let H := SolubleSubgroup.bot n
  exact ⟨successProbability H.carrier H.carrier, H, H, rfl⟩

theorem solubleProbabilities_bddBelow (n : ℕ) : BddBelow (solubleProbabilities n) := by
  refine ⟨0, ?_⟩
  rintro p ⟨H, K, rfl⟩
  exact successProbability_nonneg H.carrier K.carrier

theorem worstProbability_nonneg (n : ℕ) : 0 ≤ worstProbability n := by
  rw [worstProbability]
  exact le_csInf (solubleProbabilities_nonempty n) fun _ hp =>
    let ⟨H, K, heq⟩ := hp
    heq.symm ▸ successProbability_nonneg H.carrier K.carrier

theorem worstProbability_le_successProbability (H K : SolubleSubgroup n) :
    worstProbability n ≤ successProbability H.carrier K.carrier := by
  rw [worstProbability]
  exact csInf_le (solubleProbabilities_bddBelow n) ⟨H, K, rfl⟩

theorem worstProbability_le_one (n : ℕ) : worstProbability n ≤ 1 :=
  (worstProbability_le_successProbability (SolubleSubgroup.bot n)
    (SolubleSubgroup.bot n)).trans
      (successProbability_le_one _ _)

/-- The exact asymptotic statement required for the symmetric-group part of Problem 21.3. -/
def AsymptoticStatement : Prop :=
  Tendsto worstProbability atTop (nhds (Real.exp (-(9 : ℝ) / 2)))

end Kourovka213
