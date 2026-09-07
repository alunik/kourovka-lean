import Kourovka.Problems.P21_03.Proof.PrimeRowConditionalReduction
import Kourovka.Problems.P21_03.Proof.ParityTransporter
import Kourovka.Problems.P21_03.Proof.MaximalSolubleReduction

/-!
# Reduction for soluble subgroups of the alternating group

A subgroup of the alternating group contains no transposition, so its
transposition core is trivial.  This elementary observation is the entry
point for the parity-refined effective argument.
-/

open Subgroup Set
open scoped Pointwise

namespace Kourovka213

variable {n : ℕ}

/-- A subgroup of the alternating group contains no swaps. -/
theorem transpositionsIn_eq_empty_of_le_alternating
    (H : Subgroup (Sym n)) (hH : H ≤ alternatingGroup (Fin n)) :
    transpositionsIn H = ∅ := by
  ext g
  constructor
  · intro hg
    have hodd : Equiv.Perm.sign g = -1 := hg.1.sign_eq
    have heven : Equiv.Perm.sign g = 1 :=
      Equiv.Perm.mem_alternatingGroup.mp (hH hg.2)
    rw [hodd] at heven
    norm_num at heven
  · simp

/-- Consequently the transposition core of an alternating subgroup is
trivial. -/
theorem transpositionCore_eq_bot_of_le_alternating
    (H : Subgroup (Sym n)) (hH : H ≤ alternatingGroup (Fin n)) :
    transpositionCore H = ⊥ := by
  rw [transpositionCore, transpositionsIn_eq_empty_of_le_alternating H hH,
    Subgroup.closure_empty]

/-- For alternating subgroups, every ambient permutation is core-simple. -/
theorem goodConjugators_transpositionCore_eq_univ_of_le_alternating
    (H K : Subgroup (Sym n))
    (hH : H ≤ alternatingGroup (Fin n))
    (hK : K ≤ alternatingGroup (Fin n)) :
    goodConjugators (transpositionCore H) (transpositionCore K) =
      Finset.univ := by
  rw [transpositionCore_eq_bot_of_le_alternating H hH,
    transpositionCore_eq_bot_of_le_alternating K hK]
  ext x
  simp [mem_goodConjugators, conjugate]

/-- The core-conditioned sample space appearing in the row reduction is the
whole symmetric group when both subgroups lie in the alternating group. -/
theorem primeRowCoreSimpleSet_eq_univ_of_le_alternating
    (H K : SolubleSubgroup n)
    (hH : H.carrier ≤ alternatingGroup (Fin n))
    (hK : K.carrier ≤ alternatingGroup (Fin n)) :
    primeRowCoreSimpleSet H K = Finset.univ := by
  unfold primeRowCoreSimpleSet
  rw [← goodConjugators_transpositionCore_eq_simplePermutations H K,
    goodConjugators_transpositionCore_eq_univ_of_le_alternating
      H.carrier K.carrier hH hK]

/-- Failed ambient conjugators, with no core condition. -/
noncomputable def badConjugators
    (H K : SolubleSubgroup n) : Finset (Sym n) := by
  classical
  exact Finset.univ.filter fun x ↦
    ¬ Disjoint H.carrier (conjugate K.carrier x)

@[simp]
theorem mem_badConjugators {H K : SolubleSubgroup n} {x : Sym n} :
    x ∈ badConjugators H K ↔
      ¬ Disjoint H.carrier (conjugate K.carrier x) := by
  classical
  simp [badConjugators]

/-- In the alternating case, the extra-bad set is simply the full set of
failed conjugators, since the core condition is automatic. -/
theorem extraBadConjugators_eq_bad_of_le_alternating
    (H K : SolubleSubgroup n)
    (hH : H.carrier ≤ alternatingGroup (Fin n))
    (hK : K.carrier ≤ alternatingGroup (Fin n)) :
    extraBadConjugators H K = badConjugators H K := by
  classical
  ext x
  simp only [extraBadConjugators, Finset.mem_filter, Finset.mem_univ,
    true_and, mem_badConjugators]
  rw [transpositionCore_eq_bot_of_le_alternating H.carrier hH,
    transpositionCore_eq_bot_of_le_alternating K.carrier hK]
  simp [conjugate]

/-- Failed even conjugators for a pair of alternating subgroups. -/
noncomputable def alternatingBadConjugators
    (H K : SolubleSubgroup n) : Finset (Sym n) :=
  extraBadConjugators H K ∩ subgroupElements (alternatingGroup (Fin n))

@[simp]
theorem mem_alternatingBadConjugators
    {H K : SolubleSubgroup n} {x : Sym n} :
    x ∈ alternatingBadConjugators H K ↔
      x ∈ extraBadConjugators H K ∧ x ∈ alternatingGroup (Fin n) := by
  classical
  simp [alternatingBadConjugators]

/-- If fewer than all even permutations are bad, an even conjugator with
trivial intersection exists. -/
theorem exists_even_goodConjugator_of_alternatingBad_card_lt
    (H K : SolubleSubgroup n)
    (hH : H.carrier ≤ alternatingGroup (Fin n))
    (hK : K.carrier ≤ alternatingGroup (Fin n))
    (hcard : (alternatingBadConjugators H K).card <
      (subgroupElements (alternatingGroup (Fin n))).card) :
    ∃ x : Sym n, x ∈ alternatingGroup (Fin n) ∧
      Disjoint H.carrier (conjugate K.carrier x) := by
  classical
  obtain ⟨x, hxAlt, hxNotBad⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcard
  refine ⟨x, by simpa using hxAlt, ?_⟩
  by_contra hnot
  apply hxNotBad
  rw [mem_alternatingBadConjugators]
  refine ⟨?_, by simpa using hxAlt⟩
  rw [extraBadConjugators_eq_bad_of_le_alternating H K hH hK,
    mem_badConjugators]
  exact hnot

/-! ## Even parts of prime-row transporters -/

/-- The even part of a finite set of permutations. -/
noncomputable def evenPart (S : Finset (Sym n)) : Finset (Sym n) := by
  classical
  exact S.filter fun x ↦ x ∈ alternatingGroup (Fin n)

@[simp]
theorem mem_evenPart {S : Finset (Sym n)} {x : Sym n} :
    x ∈ evenPart S ↔ x ∈ S ∧ x ∈ alternatingGroup (Fin n) := by
  classical
  simp [evenPart]

/-- The even part of a transporter union is covered by the corresponding
even transporter pieces. -/
theorem evenPart_conjugationHits_subset_evenTransporters
    (A B : Finset (Sym n)) :
    evenPart (conjugationHits A B) ⊆
      A.biUnion fun a ↦ B.biUnion fun b ↦ evenConjugatingElements a b := by
  classical
  intro x hx
  obtain ⟨hxHit, hxEven⟩ := mem_evenPart.mp hx
  obtain ⟨a, ha, hxaB⟩ := mem_conjugationHits.mp hxHit
  rw [Finset.mem_biUnion]
  refine ⟨a, ha, ?_⟩
  rw [Finset.mem_biUnion]
  refine ⟨x * a * x⁻¹, hxaB, ?_⟩
  simp only [evenConjugatingElements, Finset.mem_filter]
  exact ⟨mem_conjugatingElements.mpr rfl, hxEven⟩

/-- Union bound for the even part, before using parity balance. -/
theorem card_evenPart_conjugationHits_le_sum_evenTransporters
    (A B : Finset (Sym n)) :
    (evenPart (conjugationHits A B)).card ≤
      ∑ a ∈ A, ∑ b ∈ B, (evenConjugatingElements a b).card := by
  classical
  calc
    (evenPart (conjugationHits A B)).card ≤
        (A.biUnion fun a ↦ B.biUnion fun b ↦
          evenConjugatingElements a b).card :=
      Finset.card_le_card
        (evenPart_conjugationHits_subset_evenTransporters A B)
    _ ≤ ∑ a ∈ A,
        (B.biUnion fun b ↦ evenConjugatingElements a b).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ a ∈ A, ∑ b ∈ B,
        (evenConjugatingElements a b).card := by
      exact Finset.sum_le_sum fun _a _ha ↦ Finset.card_biUnion_le

/-- If all component transporters are parity-balanced, the even part of
their union costs at most half the ordinary transporter union bound. -/
theorem two_mul_card_evenPart_conjugationHits_le_sum_transporters
    (A B : Finset (Sym n))
    (hbalance : ∀ a ∈ A, ∀ b ∈ B,
      2 * (evenConjugatingElements a b).card =
        (conjugatingElements a b).card) :
    2 * (evenPart (conjugationHits A B)).card ≤
      ∑ a ∈ A, ∑ b ∈ B, (conjugatingElements a b).card := by
  classical
  calc
    2 * (evenPart (conjugationHits A B)).card ≤
        2 * (∑ a ∈ A, ∑ b ∈ B,
          (evenConjugatingElements a b).card) :=
      Nat.mul_le_mul_left 2
        (card_evenPart_conjugationHits_le_sum_evenTransporters A B)
    _ = ∑ a ∈ A, ∑ b ∈ B,
        2 * (evenConjugatingElements a b).card := by
      simp_rw [Finset.mul_sum]
    _ = ∑ a ∈ A, ∑ b ∈ B,
        (conjugatingElements a b).card := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      exact hbalance a ha b hb

/-- Outside the unique unbalanced cycle type, an entire prime row has the
half-even transporter bound. -/
theorem two_mul_card_evenPart_primeRowHits_le_sum_transporters
    (A B : Finset (Sym n)) (p r : ℕ)
    (hp : p.Prime) (hr : 0 < r)
    (hcycle : ∀ a ∈ A,
      a.cycleType = Multiset.replicate r p)
    (hnotExceptional : ¬ (Odd p ∧ r = 1 ∧ n - p ≤ 1)) :
    2 * (evenPart (conjugationHits A B)).card ≤
      ∑ a ∈ A, ∑ b ∈ B, (conjugatingElements a b).card := by
  apply two_mul_card_evenPart_conjugationHits_le_sum_transporters A B
  intro a ha b _hb
  rcases transporter_parity_balanced_or_odd_single_cycle_exception
      a hp.two_le hr (hcycle a ha) with hbalanced | hexception
  · exact hbalanced b
  · exact (hnotExceptional hexception).elim

/-- At degree at least `400`, the unbalanced single-cycle exception can
only occur at support at least `401`. -/
theorem odd_single_cycle_exception_support_ge_401
    {n p r : ℕ} (hn : 400 ≤ n) (hp : p.Prime)
    (hpr : p * r ≤ n)
    (hexception : Odd p ∧ r = 1 ∧ n - p ≤ 1) :
    401 ≤ p * r := by
  obtain ⟨_hpOdd, rfl, hfixed⟩ := hexception
  simp only [mul_one] at hpr ⊢
  by_contra hnot
  have hp400 : p ≤ 400 := by omega
  have hp399 : 399 ≤ p := by omega
  interval_cases p <;> norm_num at hp

/-! ## Flipping the parity of an already-good conjugator -/

/-- Left multiplication by an element of the right-hand subgroup does not
change its conjugate. -/
theorem conjugate_mul_left_eq_of_mem
    (K : Subgroup (Sym n)) {z : Sym n} (hz : z ∈ K) (x : Sym n) :
    conjugate K (z * x) = conjugate K x := by
  ext g
  rw [conjugate, conjugate, mem_conjugate_iff, mem_conjugate_iff]
  constructor
  · intro hg
    have hmem := K.mul_mem (K.mul_mem (K.inv_mem hz) hg) hz
    convert hmem using 1 <;> group
  · intro hg
    have hmem := K.mul_mem (K.mul_mem hz hg) (K.inv_mem hz)
    convert hmem using 1 <;> group

/-- Right multiplication by an element of the left-hand subgroup preserves
triviality of the intersection. -/
theorem disjoint_conjugate_mul_right_iff_of_mem
    (H K : Subgroup (Sym n)) {z : Sym n} (hz : z ∈ H) (x : Sym n) :
    Disjoint H (conjugate K (x * z)) ↔
      Disjoint H (conjugate K x) := by
  constructor
  · intro hleft
    rw [Subgroup.disjoint_def] at hleft ⊢
    intro g hgH hgK
    let g' : Sym n := z⁻¹ * g * z
    have hg'H : g' ∈ H :=
      H.mul_mem (H.mul_mem (H.inv_mem hz) hgH) hz
    have hg'K : g' ∈ conjugate K (x * z) := by
      rw [conjugate, mem_conjugate_iff]
      rw [conjugate, mem_conjugate_iff] at hgK
      convert hgK using 1 <;> dsimp [g'] <;> group
    have hg'One := hleft hg'H hg'K
    calc
      g = z * g' * z⁻¹ := by dsimp [g']; group
      _ = z * 1 * z⁻¹ := by rw [hg'One]
      _ = 1 := by group
  · intro hright
    rw [Subgroup.disjoint_def] at hright ⊢
    intro g hgH hgK
    let g' : Sym n := z * g * z⁻¹
    have hg'H : g' ∈ H :=
      H.mul_mem (H.mul_mem hz hgH) (H.inv_mem hz)
    have hg'K : g' ∈ conjugate K x := by
      rw [conjugate, mem_conjugate_iff]
      rw [conjugate, mem_conjugate_iff] at hgK
      convert hgK using 1 <;> dsimp [g'] <;> group
    have hg'One := hright hg'H hg'K
    calc
      g = z⁻¹ * g' * z := by dsimp [g']; group
      _ = z⁻¹ * 1 * z := by rw [hg'One]
      _ = 1 := by group

/-- If the right subgroup contains an odd element, every good conjugator can
be replaced by an even one. -/
theorem exists_even_goodConjugator_of_odd_mem_right
    (H K : Subgroup (Sym n)) {z : Sym n}
    (hzK : z ∈ K) (hzOdd : Equiv.Perm.sign z = -1)
    (hgood : ∃ x : Sym n, Disjoint H (conjugate K x)) :
    ∃ x : Sym n, x ∈ alternatingGroup (Fin n) ∧
      Disjoint H (conjugate K x) := by
  obtain ⟨x, hxGood⟩ := hgood
  rcases Int.units_eq_one_or (Equiv.Perm.sign x) with hxEven | hxOdd
  · exact ⟨x, Equiv.Perm.mem_alternatingGroup.mpr hxEven, hxGood⟩
  · refine ⟨z * x, Equiv.Perm.mem_alternatingGroup.mpr ?_, ?_⟩
    · rw [Equiv.Perm.sign_mul, hzOdd, hxOdd]
      norm_num
    · rwa [conjugate_mul_left_eq_of_mem K hzK x]

/-- The analogous parity flip using an odd element of the left subgroup. -/
theorem exists_even_goodConjugator_of_odd_mem_left
    (H K : Subgroup (Sym n)) {z : Sym n}
    (hzH : z ∈ H) (hzOdd : Equiv.Perm.sign z = -1)
    (hgood : ∃ x : Sym n, Disjoint H (conjugate K x)) :
    ∃ x : Sym n, x ∈ alternatingGroup (Fin n) ∧
      Disjoint H (conjugate K x) := by
  obtain ⟨x, hxGood⟩ := hgood
  rcases Int.units_eq_one_or (Equiv.Perm.sign x) with hxEven | hxOdd
  · exact ⟨x, Equiv.Perm.mem_alternatingGroup.mpr hxEven, hxGood⟩
  · refine ⟨x * z, Equiv.Perm.mem_alternatingGroup.mpr ?_, ?_⟩
    · rw [Equiv.Perm.sign_mul, hxOdd, hzOdd]
      norm_num
    · exact
        (disjoint_conjugate_mul_right_iff_of_mem H K hzH x).mpr hxGood

/-- Failure to lie in the alternating group produces an odd element. -/
theorem exists_odd_mem_of_not_le_alternating
    (H : Subgroup (Sym n))
    (hH : ¬ H ≤ alternatingGroup (Fin n)) :
    ∃ z : Sym n, z ∈ H ∧ Equiv.Perm.sign z = -1 := by
  obtain ⟨z, hzH, hzNotAlt⟩ := SetLike.not_le_iff_exists.mp hH
  refine ⟨z, hzH, ?_⟩
  rw [Equiv.Perm.mem_alternatingGroup] at hzNotAlt
  exact (Int.units_eq_one_or (Equiv.Perm.sign z)).resolve_left hzNotAlt

/-- Alternating-group existence reduces to two maximal-soluble inputs: the
ordinary symmetric-group theorem, and its even-conjugator specialization
when both maximal overgroups themselves lie in the alternating group.  If
either overgroup contains an odd element, the preceding parity flip removes
the specialization automatically. -/
theorem all_alternating_of_all_maximalSoluble
    (hsymmetric : ∀ M N : SolubleSubgroup n,
      IsMaximalSoluble M → IsMaximalSoluble N →
        ∃ x : Sym n, Disjoint M.carrier (conjugate N.carrier x))
    (hcontained : ∀ M N : SolubleSubgroup n,
      IsMaximalSoluble M → IsMaximalSoluble N →
      M.carrier ≤ alternatingGroup (Fin n) →
      N.carrier ≤ alternatingGroup (Fin n) →
        ∃ x : Sym n, x ∈ alternatingGroup (Fin n) ∧
          Disjoint M.carrier (conjugate N.carrier x)) :
    ∀ H K : SolubleSubgroup n,
      H.carrier ≤ alternatingGroup (Fin n) →
      K.carrier ≤ alternatingGroup (Fin n) →
        ∃ x : Sym n, x ∈ alternatingGroup (Fin n) ∧
          Disjoint H.carrier (conjugate K.carrier x) := by
  intro H K _hHAlt _hKAlt
  obtain ⟨M, hHM, hMmax⟩ := exists_maximalSoluble_overgroup H
  obtain ⟨N, hKN, hNmax⟩ := exists_maximalSoluble_overgroup K
  have restrict_good :
      ∀ x : Sym n, Disjoint M.carrier (conjugate N.carrier x) →
        Disjoint H.carrier (conjugate K.carrier x) := by
    intro x hx
    exact Disjoint.mono hHM
      (smul_le_smul_left (MulAut.conj x⁻¹) hKN) hx
  by_cases hMAlt : M.carrier ≤ alternatingGroup (Fin n)
  · by_cases hNAlt : N.carrier ≤ alternatingGroup (Fin n)
    · obtain ⟨x, hxEven, hxGood⟩ :=
        hcontained M N hMmax hNmax hMAlt hNAlt
      exact ⟨x, hxEven, restrict_good x hxGood⟩
    · obtain ⟨z, hzN, hzOdd⟩ :=
        exists_odd_mem_of_not_le_alternating N.carrier hNAlt
      obtain ⟨x, hxEven, hxGood⟩ :=
        exists_even_goodConjugator_of_odd_mem_right
          M.carrier N.carrier hzN hzOdd
          (hsymmetric M N hMmax hNmax)
      exact ⟨x, hxEven, restrict_good x hxGood⟩
  · obtain ⟨z, hzM, hzOdd⟩ :=
      exists_odd_mem_of_not_le_alternating M.carrier hMAlt
    obtain ⟨x, hxEven, hxGood⟩ :=
      exists_even_goodConjugator_of_odd_mem_left
        M.carrier N.carrier hzM hzOdd
        (hsymmetric M N hMmax hNmax)
    exact ⟨x, hxEven, restrict_good x hxGood⟩

end Kourovka213
