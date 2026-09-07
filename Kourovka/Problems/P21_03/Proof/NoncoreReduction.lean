import Kourovka.Problems.P21_03.Proof.ConjugationUnionBound
import Kourovka.Problems.P21_03.Proof.CoreProbability

/-!
# Reduction of the non-core error to support slices

If the full intersection is nontrivial while the transposition-core intersection is
trivial, a witness lies outside at least one of the two cores.  Conjugation preserves
support, so a finite union bound splits the error into equal-support transporter sums.
-/

open Subgroup
open scoped Pointwise BigOperators

namespace Kourovka213

variable {n : ℕ}

/-- Elements of a permutation subgroup as a finset. -/
noncomputable def subgroupElements (H : Subgroup (Sym n)) : Finset (Sym n) := by
  classical
  exact Finset.univ.filter fun g => g ∈ H

@[simp]
theorem mem_subgroupElements {H : Subgroup (Sym n)} {g : Sym n} :
    g ∈ subgroupElements H ↔ g ∈ H := by
  classical
  simp [subgroupElements]

/-- Elements of support exactly `s`. -/
noncomputable def supportSlice (H : Subgroup (Sym n)) (s : ℕ) : Finset (Sym n) := by
  classical
  exact (subgroupElements H).filter fun g => g.support.card = s

@[simp]
theorem mem_supportSlice {H : Subgroup (Sym n)} {s : ℕ} {g : Sym n} :
    g ∈ supportSlice H s ↔ g ∈ H ∧ g.support.card = s := by
  classical
  simp [supportSlice]

/-- Elements outside the transposition core, of support exactly `s`. -/
noncomputable def outsideCoreSlice (H : Subgroup (Sym n)) (s : ℕ) : Finset (Sym n) := by
  classical
  exact (supportSlice H s).filter fun g => g ∉ transpositionCore H

@[simp]
theorem mem_outsideCoreSlice {H : Subgroup (Sym n)} {s : ℕ} {g : Sym n} :
    g ∈ outsideCoreSlice H s ↔
      g ∈ H ∧ g.support.card = s ∧ g ∉ transpositionCore H := by
  classical
  simp [outsideCoreSlice, and_assoc]

/-- No element outside the transposition core has support below three. -/
theorem three_le_of_outsideCoreSlice_nonempty (H : Subgroup (Sym n)) (s : ℕ)
    (h : (outsideCoreSlice H s).Nonempty) : 3 ≤ s := by
  obtain ⟨g, hg⟩ := h
  have hg' := mem_outsideCoreSlice.mp hg
  by_contra hs
  have hs2 : s ≤ 2 := by omega
  have hsupport2 : g.support.card ≤ 2 := hg'.2.1.trans_le hs2
  by_cases hsupport1 : g.support.card ≤ 1
  · have hone : g = 1 := Equiv.Perm.card_support_le_one.mp hsupport1
    exact hg'.2.2 (hone ▸ (transpositionCore H).one_mem)
  · have hsupportEq : g.support.card = 2 := by omega
    apply hg'.2.2
    apply Subgroup.subset_closure
    exact ⟨Equiv.Perm.card_support_eq_two.mp hsupportEq, hg'.1⟩

/-- All elements outside the transposition core. -/
noncomputable def outsideCoreElements (H : Subgroup (Sym n)) : Finset (Sym n) := by
  classical
  exact (subgroupElements H).filter fun g => g ∉ transpositionCore H

@[simp]
theorem mem_outsideCoreElements {H : Subgroup (Sym n)} {g : Sym n} :
    g ∈ outsideCoreElements H ↔ g ∈ H ∧ g ∉ transpositionCore H := by
  classical
  simp [outsideCoreElements]

private theorem conjugate_support_card (x g : Sym n) :
    (x * g * x⁻¹).support.card = g.support.card :=
  Equiv.Perm.card_support_conj

/-- Every non-core error is caught by one of two conjugation-hit events. -/
theorem extraBadConjugators_subset_noncore_hits (H K : SolubleSubgroup n) :
    extraBadConjugators H K ⊆
      conjugationHits (outsideCoreElements H.carrier) (subgroupElements K.carrier) ∪
        conjugationHits (subgroupElements H.carrier) (outsideCoreElements K.carrier) := by
  classical
  intro x hx
  have hx' :
      Disjoint (transpositionCore H.carrier)
          (conjugate (transpositionCore K.carrier) x) ∧
        ¬ Disjoint H.carrier (conjugate K.carrier x) := by
    simpa [extraBadConjugators] using hx
  have hwitness : ∃ g, g ∈ H.carrier ∧ g ∈ conjugate K.carrier x ∧ g ≠ 1 := by
    have hnot := hx'.2
    rw [Subgroup.disjoint_def] at hnot
    push Not at hnot
    exact hnot
  obtain ⟨g, hgH, hgKx, hg1⟩ := hwitness
  let k : Sym n := x * g * x⁻¹
  have hkK : k ∈ K.carrier := by
    exact (mem_conjugate_iff K.carrier x g).mp hgKx
  by_cases hgcore : g ∈ transpositionCore H.carrier
  · have hkcore : k ∉ transpositionCore K.carrier := by
      intro hk
      have hgconj : g ∈ conjugate (transpositionCore K.carrier) x :=
        (mem_conjugate_iff (transpositionCore K.carrier) x g).mpr hk
      exact hg1 (Subgroup.disjoint_def.mp hx'.1 hgcore hgconj)
    apply Finset.mem_union_right
    apply mem_conjugationHits.mpr
    exact ⟨g, mem_subgroupElements.mpr hgH,
      mem_outsideCoreElements.mpr ⟨hkK, hkcore⟩⟩
  · apply Finset.mem_union_left
    apply mem_conjugationHits.mpr
    exact ⟨g, mem_outsideCoreElements.mpr ⟨hgH, hgcore⟩,
      mem_subgroupElements.mpr hkK⟩

/-- A hit sourced outside the first core belongs to an equal-support slice. -/
theorem conjugationHits_outside_subset_supportUnion
    (H K : Subgroup (Sym n)) :
    conjugationHits (outsideCoreElements H) (subgroupElements K) ⊆
      (Finset.range (n + 1)).biUnion fun s =>
        conjugationHits (outsideCoreSlice H s) (supportSlice K s) := by
  classical
  intro x hx
  obtain ⟨g, hgout, hxgK⟩ := mem_conjugationHits.mp hx
  let s := g.support.card
  have hs : s < n + 1 := by
    apply Nat.lt_succ_of_le
    simpa [s] using g.support.card_le_univ
  apply Finset.mem_biUnion.mpr
  refine ⟨s, Finset.mem_range.mpr hs, ?_⟩
  apply mem_conjugationHits.mpr
  refine ⟨g, ?_, ?_⟩
  · exact mem_outsideCoreSlice.mpr
      ⟨(mem_outsideCoreElements.mp hgout).1, rfl,
        (mem_outsideCoreElements.mp hgout).2⟩
  · exact mem_supportSlice.mpr
      ⟨mem_subgroupElements.mp hxgK,
        conjugate_support_card x g⟩

/-- The symmetric equal-support decomposition when the target lies outside its core. -/
theorem conjugationHits_targetOutside_subset_supportUnion
    (H K : Subgroup (Sym n)) :
    conjugationHits (subgroupElements H) (outsideCoreElements K) ⊆
      (Finset.range (n + 1)).biUnion fun s =>
        conjugationHits (supportSlice H s) (outsideCoreSlice K s) := by
  classical
  intro x hx
  obtain ⟨g, hgH, hxgout⟩ := mem_conjugationHits.mp hx
  let s := g.support.card
  have hs : s < n + 1 := by
    apply Nat.lt_succ_of_le
    simpa [s] using g.support.card_le_univ
  apply Finset.mem_biUnion.mpr
  refine ⟨s, Finset.mem_range.mpr hs, ?_⟩
  apply mem_conjugationHits.mpr
  refine ⟨g, mem_supportSlice.mpr ⟨mem_subgroupElements.mp hgH, rfl⟩, ?_⟩
  have hout := mem_outsideCoreElements.mp hxgout
  exact mem_outsideCoreSlice.mpr
    ⟨hout.1, conjugate_support_card x g, hout.2⟩

/-- Exact finite cardinal reduction to the two support-sliced transporter sums. -/
theorem card_extraBadConjugators_le_support_sums (H K : SolubleSubgroup n) :
    (extraBadConjugators H K).card ≤
      (∑ s ∈ Finset.range (n + 1),
          (conjugationHits (outsideCoreSlice H.carrier s)
            (supportSlice K.carrier s)).card) +
        (∑ s ∈ Finset.range (n + 1),
          (conjugationHits (supportSlice H.carrier s)
            (outsideCoreSlice K.carrier s)).card) := by
  classical
  let hitHK := conjugationHits (outsideCoreElements H.carrier)
    (subgroupElements K.carrier)
  let hitKH := conjugationHits (subgroupElements H.carrier)
    (outsideCoreElements K.carrier)
  calc
    (extraBadConjugators H K).card ≤ (hitHK ∪ hitKH).card :=
      Finset.card_le_card (extraBadConjugators_subset_noncore_hits H K)
    _ ≤ hitHK.card + hitKH.card := Finset.card_union_le _ _
    _ ≤
        (∑ s ∈ Finset.range (n + 1),
            (conjugationHits (outsideCoreSlice H.carrier s)
              (supportSlice K.carrier s)).card) +
          (∑ s ∈ Finset.range (n + 1),
            (conjugationHits (supportSlice H.carrier s)
              (outsideCoreSlice K.carrier s)).card) := by
      apply Nat.add_le_add
      · exact (Finset.card_le_card
          (conjugationHits_outside_subset_supportUnion H.carrier K.carrier)).trans
            Finset.card_biUnion_le
      · exact (Finset.card_le_card
          (conjugationHits_targetOutside_subset_supportUnion H.carrier K.carrier)).trans
            Finset.card_biUnion_le

/-- The class/centralizer estimate applied to an outside-core source slice. -/
theorem card_noncoreSourceHit_le (H K : Subgroup (Sym n)) (s : ℕ) :
    (conjugationHits (outsideCoreSlice H s) (supportSlice K s)).card ≤
      (outsideCoreSlice H s).card * (supportSlice K s).card *
        ((n - s).factorial * s ^ (s / 2)) := by
  apply card_conjugationHits_le_of_source_support
  intro a ha
  exact (mem_outsideCoreSlice.mp ha).2.1

/-- The corresponding bound when the target slice lies outside its core. -/
theorem card_noncoreTargetHit_le (H K : Subgroup (Sym n)) (s : ℕ) :
    (conjugationHits (supportSlice H s) (outsideCoreSlice K s)).card ≤
      (supportSlice H s).card * (outsideCoreSlice K s).card *
        ((n - s).factorial * s ^ (s / 2)) := by
  apply card_conjugationHits_le_of_source_support
  intro a ha
  exact (mem_supportSlice.mp ha).2

/-- Fully numerical reduction of the non-core error.  The remaining group-theoretic
input is precisely a pair of bounds on the two slice cardinalities. -/
theorem card_extraBadConjugators_le_support_products (H K : SolubleSubgroup n) :
    (extraBadConjugators H K).card ≤
      (∑ s ∈ Finset.range (n + 1),
          (outsideCoreSlice H.carrier s).card * (supportSlice K.carrier s).card *
            ((n - s).factorial * s ^ (s / 2))) +
        (∑ s ∈ Finset.range (n + 1),
          (supportSlice H.carrier s).card * (outsideCoreSlice K.carrier s).card *
            ((n - s).factorial * s ^ (s / 2))) := by
  refine (card_extraBadConjugators_le_support_sums H K).trans ?_
  apply Nat.add_le_add <;> apply Finset.sum_le_sum <;>
    intro s _hs
  · exact card_noncoreSourceHit_le H.carrier K.carrier s
  · exact card_noncoreTargetHit_le H.carrier K.carrier s

end Kourovka213
