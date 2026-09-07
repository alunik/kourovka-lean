import Kourovka.Problems.P21_03.Proof.NoncoreReduction
import Kourovka.Problems.P21_03.Proof.PrimeOrderReduction

/-!
# Exact reduction to prime-cycle transporter rows

The effective estimate only sums prime-order rows.  This file proves that
those rows cover every non-core failure, before any numerical majorant is
applied.
-/

open Subgroup
open scoped BigOperators Pointwise

namespace Kourovka213

variable {n : ℕ}

/-- Elements of `H` of prime order `p` and support `p*r`. -/
noncomputable def primeRowSlice
    (H : Subgroup (Sym n)) (p r : ℕ) : Finset (Sym n) := by
  classical
  exact (subgroupElements H).filter fun g ↦
    orderOf g = p ∧ g.cycleType = Multiset.replicate r p ∧
      g.support.card = p * r

@[simp]
theorem mem_primeRowSlice
    {H : Subgroup (Sym n)} {p r : ℕ} {g : Sym n} :
    g ∈ primeRowSlice H p r ↔
      g ∈ H ∧ orderOf g = p ∧
        g.cycleType = Multiset.replicate r p ∧
        g.support.card = p * r := by
  classical
  simp [primeRowSlice, and_assoc]

/-- The part of a prime row outside the transposition core. -/
noncomputable def outsideCorePrimeRowSlice
    (H : Subgroup (Sym n)) (p r : ℕ) : Finset (Sym n) := by
  classical
  exact (primeRowSlice H p r).filter fun g ↦ g ∉ transpositionCore H

@[simp]
theorem mem_outsideCorePrimeRowSlice
    {H : Subgroup (Sym n)} {p r : ℕ} {g : Sym n} :
    g ∈ outsideCorePrimeRowSlice H p r ↔
      g ∈ H ∧ orderOf g = p ∧
        g.cycleType = Multiset.replicate r p ∧
        g.support.card = p * r ∧
        g ∉ transpositionCore H := by
  classical
  simp [outsideCorePrimeRowSlice, and_assoc]

/-- All source-outside prime rows in the finite ambient range. -/
noncomputable def sourceOutsidePrimeRowHits
    (H K : Subgroup (Sym n)) : Finset (Sym n) := by
  classical
  exact (Finset.range (n + 1)).biUnion fun p ↦
    (Finset.range (n + 1)).biUnion fun r ↦
      conjugationHits (outsideCorePrimeRowSlice H p r)
        (primeRowSlice K p r)

/-- All target-outside prime rows in the finite ambient range. -/
noncomputable def targetOutsidePrimeRowHits
    (H K : Subgroup (Sym n)) : Finset (Sym n) := by
  classical
  exact (Finset.range (n + 1)).biUnion fun p ↦
    (Finset.range (n + 1)).biUnion fun r ↦
      conjugationHits (primeRowSlice H p r)
        (outsideCorePrimeRowSlice K p r)

private theorem conjugate_orderOf (x g : Sym n) :
    orderOf (x * g * x⁻¹) = orderOf g := by
  apply (SemiconjBy.orderOf_eq x ?_).symm
  show x * g = (x * g * x⁻¹) * x
  group

private theorem conjugate_support_card (x g : Sym n) :
    (x * g * x⁻¹).support.card = g.support.card :=
  Equiv.Perm.card_support_conj

/-- Exact centralizer size for cycle type `p^r`. -/
theorem natCard_centralizer_primeRow
    (g : Sym n) (p r : ℕ) (hr : 0 < r)
    (hcycle : g.cycleType = Multiset.replicate r p) :
    Nat.card (Subgroup.centralizer ({g} : Set (Sym n))) =
      (n - p * r).factorial * p ^ r * r.factorial := by
  rw [Equiv.Perm.nat_card_centralizer, Fintype.card_fin, hcycle]
  simp [hr.ne', Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

/-- Every transporter sourced in a `p^r` row has the exact prime-row
centralizer as a uniform upper bound. -/
theorem card_conjugatingElements_primeRow_le
    (a b : Sym n) (p r : ℕ) (hr : 0 < r)
    (hcycle : a.cycleType = Multiset.replicate r p) :
    (conjugatingElements a b).card ≤
      (n - p * r).factorial * p ^ r * r.factorial := by
  by_cases hab : IsConj a b
  · rw [card_conjugatingElements_eq_centralizer a b hab,
      natCard_centralizer_primeRow a p r hr hcycle]
  · rw [card_conjugatingElements_eq_zero a b hab]
    exact Nat.zero_le _

/-- Source-outside prime-row transporter bound. -/
theorem card_sourceOutsidePrimeRowHit_le
    (H K : Subgroup (Sym n)) (p r : ℕ) (hr : 0 < r) :
    (conjugationHits (outsideCorePrimeRowSlice H p r)
      (primeRowSlice K p r)).card ≤
      (outsideCorePrimeRowSlice H p r).card *
        (primeRowSlice K p r).card *
        ((n - p * r).factorial * p ^ r * r.factorial) := by
  apply card_conjugationHits_le_mul
  intro a ha b _hb
  exact card_conjugatingElements_primeRow_le a b p r hr
    (mem_outsideCorePrimeRowSlice.mp ha).2.2.1

/-- Target-outside prime-row transporter bound. -/
theorem card_targetOutsidePrimeRowHit_le
    (H K : Subgroup (Sym n)) (p r : ℕ) (hr : 0 < r) :
    (conjugationHits (primeRowSlice H p r)
      (outsideCorePrimeRowSlice K p r)).card ≤
      (primeRowSlice H p r).card *
        (outsideCorePrimeRowSlice K p r).card *
        ((n - p * r).factorial * p ^ r * r.factorial) := by
  apply card_conjugationHits_le_mul
  intro a ha b _hb
  exact card_conjugatingElements_primeRow_le a b p r hr
    (mem_primeRowSlice.mp ha).2.2.1

/-- Every full-intersection failure left after conditioning on core
simplicity belongs to one of the two finite prime-row unions. -/
theorem extraBadConjugators_subset_primeRowHits (H K : SolubleSubgroup n) :
    extraBadConjugators H K ⊆
      sourceOutsidePrimeRowHits H.carrier K.carrier ∪
        targetOutsidePrimeRowHits H.carrier K.carrier := by
  classical
  intro x hx
  have hx' :
      Disjoint (transpositionCore H.carrier)
          (conjugate (transpositionCore K.carrier) x) ∧
        ¬ Disjoint H.carrier (conjugate K.carrier x) := by
    simpa [extraBadConjugators] using hx
  obtain ⟨p, r, hp, hr, g, hgH, hgKx, hgOrder, hcycle, hsupport⟩ :=
    exists_prime_cycle_row_mem_of_not_disjoint
      H.carrier (conjugate K.carrier x) hx'.2
  let k : Sym n := x * g * x⁻¹
  have hkK : k ∈ K.carrier :=
    (mem_conjugate_iff K.carrier x g).mp hgKx
  have hkOrder : orderOf k = p := by
    rw [conjugate_orderOf x g, hgOrder]
  have hkSupport : k.support.card = p * r := by
    rw [conjugate_support_card x g, hsupport]
  have hkCycle : k.cycleType = Multiset.replicate r p := by
    rw [Equiv.Perm.cycleType_conj, hcycle]
  have hpr_le : p * r ≤ n := by
    rw [← hsupport]
    simpa using g.support.card_le_univ
  have hp_le : p ≤ n := by
    calc
      p = p * 1 := by simp
      _ ≤ p * r := Nat.mul_le_mul_left p hr
      _ ≤ n := hpr_le
  have hr_le : r ≤ n := by
    calc
      r = 1 * r := by simp
      _ ≤ p * r := Nat.mul_le_mul_right r hp.one_le
      _ ≤ n := hpr_le
  have hpRange : p ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
  have hrRange : r ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
  by_cases hgCore : g ∈ transpositionCore H.carrier
  · have hkNotCore : k ∉ transpositionCore K.carrier := by
      intro hkCore
      have hgConj : g ∈ conjugate (transpositionCore K.carrier) x :=
        (mem_conjugate_iff (transpositionCore K.carrier) x g).mpr hkCore
      have hgOne := Subgroup.disjoint_def.mp hx'.1 hgCore hgConj
      exact hp.ne_one (hgOrder ▸ orderOf_eq_one_iff.mpr hgOne)
    apply Finset.mem_union_right
    apply Finset.mem_biUnion.mpr
    refine ⟨p, hpRange, ?_⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨r, hrRange, ?_⟩
    apply mem_conjugationHits.mpr
    exact ⟨g, mem_primeRowSlice.mpr ⟨hgH, hgOrder, hcycle, hsupport⟩,
      mem_outsideCorePrimeRowSlice.mpr
        ⟨hkK, hkOrder, hkCycle, hkSupport, hkNotCore⟩⟩
  · apply Finset.mem_union_left
    apply Finset.mem_biUnion.mpr
    refine ⟨p, hpRange, ?_⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨r, hrRange, ?_⟩
    apply mem_conjugationHits.mpr
    exact ⟨g, mem_outsideCorePrimeRowSlice.mpr
        ⟨hgH, hgOrder, hcycle, hsupport, hgCore⟩,
      mem_primeRowSlice.mpr ⟨hkK, hkOrder, hkCycle, hkSupport⟩⟩

/-- Cardinal union bound over the exhaustive finite prime rows. -/
theorem card_extraBadConjugators_le_primeRowSums (H K : SolubleSubgroup n) :
    (extraBadConjugators H K).card ≤
      (∑ p ∈ Finset.range (n + 1), ∑ r ∈ Finset.range (n + 1),
        (conjugationHits (outsideCorePrimeRowSlice H.carrier p r)
          (primeRowSlice K.carrier p r)).card) +
      (∑ p ∈ Finset.range (n + 1), ∑ r ∈ Finset.range (n + 1),
        (conjugationHits (primeRowSlice H.carrier p r)
          (outsideCorePrimeRowSlice K.carrier p r)).card) := by
  classical
  calc
    (extraBadConjugators H K).card ≤
        (sourceOutsidePrimeRowHits H.carrier K.carrier ∪
          targetOutsidePrimeRowHits H.carrier K.carrier).card :=
      Finset.card_le_card (extraBadConjugators_subset_primeRowHits H K)
    _ ≤ (sourceOutsidePrimeRowHits H.carrier K.carrier).card +
          (targetOutsidePrimeRowHits H.carrier K.carrier).card :=
      Finset.card_union_le _ _
    _ ≤ _ := by
      apply Nat.add_le_add
      · exact Finset.card_biUnion_le.trans
          (Finset.sum_le_sum fun _ _ ↦ Finset.card_biUnion_le)
      · exact Finset.card_biUnion_le.trans
          (Finset.sum_le_sum fun _ _ ↦ Finset.card_biUnion_le)

/-- A zero-support row has no element outside the transposition core. -/
theorem outsideCorePrimeRowSlice_zero
    (H : Subgroup (Sym n)) (p : ℕ) :
    outsideCorePrimeRowSlice H p 0 = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro g hg
  have hg' := mem_outsideCorePrimeRowSlice.mp hg
  have hzero : g.support.card = 0 := by simpa using hg'.2.2.2.1
  have hone : g = 1 := Equiv.Perm.card_support_eq_zero.mp hzero
  exact hg'.2.2.2.2 (hone ▸ (transpositionCore H).one_mem)

private theorem conjugationHits_empty_right
    (A : Finset (Sym n)) : conjugationHits A ∅ = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨a, _ha, hmem⟩ := mem_conjugationHits.mp hx
  simpa using hmem

private theorem conjugationHits_empty_left
    (B : Finset (Sym n)) : conjugationHits ∅ B = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨a, ha, _hmem⟩ := mem_conjugationHits.mp hx
  simpa using ha

/-- Fully numerical prime-row reduction with the exact centralizer factor
`(n-p*r)! p^r r!`.  The remaining inputs are bounds on the two row-slice
cardinalities. -/
theorem card_extraBadConjugators_le_primeRowProducts
    (H K : SolubleSubgroup n) :
    (extraBadConjugators H K).card ≤
      (∑ p ∈ Finset.range (n + 1), ∑ r ∈ Finset.range (n + 1),
        (outsideCorePrimeRowSlice H.carrier p r).card *
          (primeRowSlice K.carrier p r).card *
          ((n - p * r).factorial * p ^ r * r.factorial)) +
      (∑ p ∈ Finset.range (n + 1), ∑ r ∈ Finset.range (n + 1),
        (primeRowSlice H.carrier p r).card *
          (outsideCorePrimeRowSlice K.carrier p r).card *
          ((n - p * r).factorial * p ^ r * r.factorial)) := by
  refine (card_extraBadConjugators_le_primeRowSums H K).trans ?_
  apply Nat.add_le_add <;>
    apply Finset.sum_le_sum <;> intro p _hp <;>
    apply Finset.sum_le_sum <;> intro r _hr
  · by_cases hr0 : r = 0
    · subst r
      rw [outsideCorePrimeRowSlice_zero,
        conjugationHits_empty_left]
      simp
    · exact card_sourceOutsidePrimeRowHit_le H.carrier K.carrier p r
        (Nat.pos_of_ne_zero hr0)
  · by_cases hr0 : r = 0
    · subst r
      rw [outsideCorePrimeRowSlice_zero,
        conjugationHits_empty_right]
      simp
    · exact card_targetOutsidePrimeRowHit_le H.carrier K.carrier p r
        (Nat.pos_of_ne_zero hr0)

end Kourovka213
