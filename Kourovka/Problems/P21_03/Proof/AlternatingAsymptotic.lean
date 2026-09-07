import Kourovka.Problems.P21_03.Proof.Asymptotic
import Kourovka.Problems.P21_03.Proof.AlternatingReduction

/-!
# Eventual existence in the alternating group

`asymptoticStatement` gives the symmetric-group limit required in
Kourovka Notebook Problem 21.3.  This file supplies the remaining parity
step in Lean.

For maximal soluble overgroups there are two cases.  If either overgroup
contains an odd permutation, an arbitrary good conjugator can be parity
flipped.  If both overgroups lie in `A_n`, their transposition cores are
trivial.  Maximality identifies each group with its forest envelope, so the
uniform noncore error tends to zero; once it is below one half, fewer than
all even permutations are bad.
-/

open Filter
open scoped Topology

namespace Kourovka213

variable {n : ℕ}

/-- The finite set of elements of a subgroup has the cardinality of the
subgroup subtype. -/
theorem card_subgroupElements (H : Subgroup (Sym n)) :
    (subgroupElements H).card = Nat.card H := by
  classical
  let e : {g // g ∈ subgroupElements H} ≃ H :=
    { toFun := fun g => ⟨g.1, mem_subgroupElements.mp g.2⟩
      invFun := fun g => ⟨g.1, mem_subgroupElements.mpr g.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  calc
    (subgroupElements H).card = Nat.card {g // g ∈ subgroupElements H} := by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ = Nat.card H := Nat.card_congr e

/-- Positive worst-case probability gives an actual good conjugator for
every soluble pair in that degree. -/
theorem exists_goodConjugator_of_worstProbability_pos
    (hpos : 0 < worstProbability n) (H K : SolubleSubgroup n) :
    ∃ x : Sym n, Disjoint H.carrier (conjugate K.carrier x) := by
  have hsuccess : 0 < successProbability H.carrier K.carrier :=
    hpos.trans_le (worstProbability_le_successProbability H K)
  have hden : (0 : ℝ) < Fintype.card (Sym n) := by positivity
  have hprod := mul_pos hsuccess hden
  have hcancel :
      successProbability H.carrier K.carrier * Fintype.card (Sym n) =
        ((goodConjugators H.carrier K.carrier).card : ℝ) := by
    rw [successProbability, div_mul_cancel₀]
    exact ne_of_gt hden
  have hcardReal :
      (0 : ℝ) < ((goodConjugators H.carrier K.carrier).card : ℝ) := by
    rwa [hcancel] at hprod
  have hcard : 0 < (goodConjugators H.carrier K.carrier).card := by
    exact_mod_cast hcardReal
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hcard
  exact ⟨x, mem_goodConjugators.mp hx⟩

/-- The symmetric asymptotic theorem is eventually strong enough to give a
good conjugator for every soluble pair. -/
theorem eventually_all_symmetric_goodConjugators :
    ∀ᶠ n : ℕ in atTop, ∀ H K : SolubleSubgroup n,
      ∃ x : Sym n, Disjoint H.carrier (conjugate K.carrier x) := by
  have hpositive : ∀ᶠ n : ℕ in atTop, 0 < worstProbability n :=
    asymptoticStatement.eventually
      (Ioi_mem_nhds (Real.exp_pos (-(9 : ℝ) / 2)))
  filter_upwards [hpositive] with n hn
  exact fun H K => exists_goodConjugator_of_worstProbability_pos hn H K

/-- A maximal soluble subgroup inherits the unconditional support bounds of
its forest envelope. -/
theorem supportBoundsFor_of_isMaximalSoluble
    (M : SolubleSubgroup n) (hM : IsMaximalSoluble M) (hn : 0 < n) :
    SupportBoundsFor (16 * (256 ^ 2)) M := by
  have h := M.forestEnvelope_supportBounds hn
  rw [forestEnvelope_eq_of_isMaximalSoluble' M hM hn] at h
  exact h

/-- If both maximal soluble groups lie in `A_n`, the vanishing forest error
eventually leaves an even good conjugator. -/
theorem exists_even_goodConjugator_of_maximal_alternating_noncoreError_lt_half
    (hn : 2 ≤ n)
    (herror : noncoreErrorBound (16 * (256 ^ 2)) n < (1 : ℝ) / 2)
    (M N : SolubleSubgroup n)
    (hMmax : IsMaximalSoluble M) (hNmax : IsMaximalSoluble N)
    (hMAlt : M.carrier ≤ alternatingGroup (Fin n))
    (hNAlt : N.carrier ≤ alternatingGroup (Fin n)) :
    ∃ x : Sym n, x ∈ alternatingGroup (Fin n) ∧
      Disjoint M.carrier (conjugate N.carrier x) := by
  have hnpos : 0 < n := by omega
  have hMbound := supportBoundsFor_of_isMaximalSoluble M hMmax hnpos
  have hNbound := supportBoundsFor_of_isMaximalSoluble N hNmax hnpos
  have hprob : extraBadProbability M N < (1 : ℝ) / 2 :=
    (extraBadProbability_le_noncoreErrorBound M N hMbound hNbound).trans_lt
      herror
  have hden : (0 : ℝ) < Fintype.card (Sym n) := by positivity
  have hratio :
      ((extraBadConjugators M N).card : ℝ) <
        (1 / 2 : ℝ) * Fintype.card (Sym n) := by
    exact (div_lt_iff₀ hden).mp (by
      simpa [extraBadProbability] using hprob)
  have htwiceReal :
      (2 : ℝ) * (extraBadConjugators M N).card <
        Fintype.card (Sym n) := by
    nlinarith
  have htwice :
      2 * (extraBadConjugators M N).card < Fintype.card (Sym n) := by
    exact_mod_cast htwiceReal
  letI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  have hAltCard :
      2 * Nat.card (alternatingGroup (Fin n)) =
        Fintype.card (Sym n) := by
    simpa [Nat.card_eq_fintype_card] using
      (two_mul_nat_card_alternatingGroup (α := Fin n))
  have hextraLtAlt :
      (extraBadConjugators M N).card <
        (subgroupElements (alternatingGroup (Fin n))).card := by
    rw [card_subgroupElements]
    rw [← Nat.mul_lt_mul_left (by decide : 0 < 2), hAltCard]
    exact htwice
  have hbadLtAlt :
      (alternatingBadConjugators M N).card <
        (subgroupElements (alternatingGroup (Fin n))).card := by
    exact (Finset.card_le_card (Finset.inter_subset_left)).trans_lt hextraLtAlt
  exact exists_even_goodConjugator_of_alternatingBad_card_lt
    M N hMAlt hNAlt hbadLtAlt

/-- The full alternating-group existence assertion holds in every
sufficiently large degree. -/
theorem eventually_all_alternating_goodConjugators :
    ∀ᶠ n : ℕ in atTop, ∀ H K : SolubleSubgroup n,
      H.carrier ≤ alternatingGroup (Fin n) →
      K.carrier ≤ alternatingGroup (Fin n) →
        ∃ x : Sym n, x ∈ alternatingGroup (Fin n) ∧
          Disjoint H.carrier (conjugate K.carrier x) := by
  have hpositive : ∀ᶠ n : ℕ in atTop, 0 < worstProbability n :=
    asymptoticStatement.eventually
      (Ioi_mem_nhds (Real.exp_pos (-(9 : ℝ) / 2)))
  have herror : ∀ᶠ n : ℕ in atTop,
      noncoreErrorBound (16 * (256 ^ 2)) n < (1 : ℝ) / 2 :=
    (tendsto_noncoreErrorBound_zero (16 * (256 ^ 2))).eventually
      (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [hpositive, herror, eventually_ge_atTop 2] with n hnPos hnError hn
  apply all_alternating_of_all_maximalSoluble
  · intro M N _hMmax _hNmax
    exact exists_goodConjugator_of_worstProbability_pos hnPos M N
  · intro M N hMmax hNmax hMAlt hNAlt
    exact exists_even_goodConjugator_of_maximal_alternating_noncoreError_lt_half
      hn hnError M N hMmax hNmax hMAlt hNAlt

/-- Both parts of the first question in Problem 21.3, packaged as one
eventual statement. -/
theorem eventually_kourovka213 :
    ∀ᶠ n : ℕ in atTop,
      (∀ H K : SolubleSubgroup n,
        ∃ x : Sym n, Disjoint H.carrier (conjugate K.carrier x)) ∧
      (∀ H K : SolubleSubgroup n,
        H.carrier ≤ alternatingGroup (Fin n) →
        K.carrier ≤ alternatingGroup (Fin n) →
          ∃ x : Sym n, x ∈ alternatingGroup (Fin n) ∧
            Disjoint H.carrier (conjugate K.carrier x)) := by
  filter_upwards [eventually_all_symmetric_goodConjugators,
    eventually_all_alternating_goodConjugators] with n hSym hAlt
  exact ⟨hSym, hAlt⟩

end Kourovka213
