import Kourovka.Problems.P21_03.Proof.ConjugationUnionBound
import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer

/-!
# Parity balance in permutation transporters

Right multiplication by an odd element centralizing the source permutation
pairs the even and odd halves of every conjugating transporter.  For a
permutation of cycle type `p^r`, such an odd centralizer element exists unless
`p` is odd, `r = 1`, and there is at most one fixed point.
-/

open Subgroup Set

namespace Kourovka213

universe u

variable {X : Type u} [Fintype X] [DecidableEq X]

/-- Even elements of an abstract conjugating transporter. -/
abbrev EvenConjugating (a b : Equiv.Perm X) :=
  {x : Conjugating a b // Equiv.Perm.sign x.1 = 1}

/-- Odd elements of an abstract conjugating transporter. -/
abbrev OddConjugating (a b : Equiv.Perm X) :=
  {x : Conjugating a b // Equiv.Perm.sign x.1 = -1}

noncomputable local instance conjugatingFintype (a b : Equiv.Perm X) :
    Fintype (Conjugating a b) := by
  classical
  unfold Conjugating
  infer_instance

/-- Right multiplication by an odd centralizer element exchanges the two
parity classes in every transporter from `a` to `b`. -/
noncomputable def evenConjugatingEquivOdd
    (a b tau : Equiv.Perm X) (hcomm : tau * a = a * tau)
    (htau : Equiv.Perm.sign tau = -1) :
    EvenConjugating a b ≃ OddConjugating a b where
  toFun x := ⟨⟨x.1.1 * tau, by
    calc
      (x.1.1 * tau) * a * (x.1.1 * tau)⁻¹ =
          x.1.1 * (tau * a) * tau⁻¹ * x.1.1⁻¹ := by group
      _ = x.1.1 * (a * tau) * tau⁻¹ * x.1.1⁻¹ := by rw [hcomm]
      _ = x.1.1 * a * x.1.1⁻¹ := by group
      _ = b := x.1.2⟩, by
        change Equiv.Perm.sign (x.1.1 * tau) = -1
        rw [Equiv.Perm.sign_mul, x.2, htau]
        norm_num⟩
  invFun x := ⟨⟨x.1.1 * tau⁻¹, by
    have hcommInv : tau⁻¹ * a = a * tau⁻¹ := by
      calc
        tau⁻¹ * a = tau⁻¹ * (a * tau) * tau⁻¹ := by group
        _ = tau⁻¹ * (tau * a) * tau⁻¹ := by rw [hcomm]
        _ = a * tau⁻¹ := by group
    calc
      (x.1.1 * tau⁻¹) * a * (x.1.1 * tau⁻¹)⁻¹ =
          x.1.1 * (tau⁻¹ * a) * tau * x.1.1⁻¹ := by group
      _ = x.1.1 * (a * tau⁻¹) * tau * x.1.1⁻¹ := by
        rw [hcommInv]
      _ = x.1.1 * a * x.1.1⁻¹ := by group
      _ = b := x.1.2⟩, by
        change Equiv.Perm.sign (x.1.1 * tau⁻¹) = 1
        rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_inv, x.2, htau]
        norm_num⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    simp
  right_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    simp

/-- Every transporter is the disjoint union of its even and odd parts. -/
theorem natCard_conjugating_eq_even_add_odd (a b : Equiv.Perm X) :
    Nat.card (Conjugating a b) =
      Nat.card (EvenConjugating a b) + Nat.card (OddConjugating a b) := by
  classical
  let even : Finset (Conjugating a b) := Finset.univ.filter fun x ↦
    Equiv.Perm.sign x.1 = 1
  let odd : Finset (Conjugating a b) := Finset.univ.filter fun x ↦
    Equiv.Perm.sign x.1 = -1
  have hunion : even ∪ odd = Finset.univ := by
    ext x
    simp only [even, odd, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · intro _
      trivial
    · intro _
      exact Int.units_eq_one_or (Equiv.Perm.sign x.1)
  have hdisj : Disjoint even odd := by
    refine Finset.disjoint_left.mpr ?_
    intro x hx hy
    have hx' := (Finset.mem_filter.mp hx).2
    have hy' := (Finset.mem_filter.mp hy).2
    rw [hx'] at hy'
    norm_num at hy'
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Nat.card_eq_fintype_card, Fintype.card_subtype,
    Fintype.card_subtype]
  change Fintype.card (Conjugating a b) = even.card + odd.card
  calc
    Fintype.card (Conjugating a b) = (Finset.univ : Finset (Conjugating a b)).card :=
      Finset.card_univ.symm
    _ = (even ∪ odd).card := congrArg Finset.card hunion.symm
    _ = even.card + odd.card := Finset.card_union_of_disjoint hdisj

/-- An odd source-centralizer element makes every transporter parity-balanced. -/
theorem two_mul_natCard_evenConjugating_eq_natCard_conjugating
    (a b tau : Equiv.Perm X) (hcomm : tau * a = a * tau)
    (htau : Equiv.Perm.sign tau = -1) :
    2 * Nat.card (EvenConjugating a b) = Nat.card (Conjugating a b) := by
  have hcard : Nat.card (EvenConjugating a b) =
      Nat.card (OddConjugating a b) :=
    Nat.card_congr (evenConjugatingEquivOdd a b tau hcomm htau)
  rw [natCard_conjugating_eq_even_add_odd, ← hcard]
  omega

section Fin

variable {n p r : ℕ}

/-- Even conjugators in the finset transporter used by the union bound. -/
noncomputable def evenConjugatingElements (a b : Equiv.Perm (Fin n)) :
    Finset (Equiv.Perm (Fin n)) := by
  classical
  exact (conjugatingElements a b).filter fun x ↦
    x ∈ alternatingGroup (Fin n)

noncomputable def conjugatingElementsSubtypeEquiv (a b : Equiv.Perm (Fin n)) :
    {x // x ∈ conjugatingElements a b} ≃ Conjugating a b where
  toFun x := ⟨x.1, mem_conjugatingElements.mp x.2⟩
  invFun x := ⟨x.1, mem_conjugatingElements.mpr x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def evenConjugatingElementsSubtypeEquiv
    (a b : Equiv.Perm (Fin n)) :
    {x // x ∈ evenConjugatingElements a b} ≃ EvenConjugating a b := by
  classical
  exact
    { toFun := fun x ↦ ⟨⟨x.1, mem_conjugatingElements.mp
          (Finset.mem_filter.mp x.2).1⟩,
        Equiv.Perm.mem_alternatingGroup.mp (Finset.mem_filter.mp x.2).2⟩
      invFun := fun x ↦ ⟨x.1.1, Finset.mem_filter.mpr
        ⟨mem_conjugatingElements.mpr x.1.2,
          Equiv.Perm.mem_alternatingGroup.mpr x.2⟩⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }

private theorem card_conjugatingElements_eq_natCard_conjugating
    (a b : Equiv.Perm (Fin n)) :
    (conjugatingElements a b).card = Nat.card (Conjugating a b) := by
  classical
  calc
    (conjugatingElements a b).card =
        Nat.card {x // x ∈ conjugatingElements a b} := by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ = Nat.card (Conjugating a b) :=
      Nat.card_congr (conjugatingElementsSubtypeEquiv a b)

private theorem card_evenConjugatingElements_eq_natCard_evenConjugating
    (a b : Equiv.Perm (Fin n)) :
    (evenConjugatingElements a b).card = Nat.card (EvenConjugating a b) := by
  classical
  calc
    (evenConjugatingElements a b).card =
        Nat.card {x // x ∈ evenConjugatingElements a b} := by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ = Nat.card (EvenConjugating a b) :=
      Nat.card_congr (evenConjugatingElementsSubtypeEquiv a b)

/-- Finset form of transporter parity balance. -/
theorem two_mul_card_evenConjugatingElements_eq_card_conjugatingElements
    (a b tau : Equiv.Perm (Fin n))
    (htauCentral : tau ∈ Subgroup.centralizer ({a} : Set (Equiv.Perm (Fin n))))
    (htauOdd : Equiv.Perm.sign tau = -1) :
    2 * (evenConjugatingElements a b).card =
      (conjugatingElements a b).card := by
  rw [card_evenConjugatingElements_eq_natCard_evenConjugating,
    card_conjugatingElements_eq_natCard_conjugating]
  apply two_mul_natCard_evenConjugating_eq_natCard_conjugating a b tau
  · exact mem_centralizer_singleton_iff.mp htauCentral
  · exact htauOdd

/-- The three explicit sources of an odd centralizer involution for cycle type
`p^r`: an even constituent cycle, an interchange of two equal cycles, or a
swap of two fixed points.  Mathlib's centralizer criterion packages those
three constructions. -/
theorem exists_odd_mem_centralizer_of_replicate_cycleType
    (g : Equiv.Perm (Fin n)) (hp : 2 ≤ p) (hr : 0 < r)
    (hcycle : g.cycleType = Multiset.replicate r p)
    (hsource : Even p ∨ 2 ≤ r ∨ p * r + 2 ≤ n) :
    ∃ tau : Equiv.Perm (Fin n),
      tau ∈ Subgroup.centralizer ({g} : Set (Equiv.Perm (Fin n))) ∧
        Equiv.Perm.sign tau = -1 := by
  classical
  by_contra hnone
  have hle : Subgroup.centralizer ({g} : Set (Equiv.Perm (Fin n))) ≤
      alternatingGroup (Fin n) := by
    intro tau htau
    rw [Equiv.Perm.mem_alternatingGroup]
    rcases Int.units_eq_one_or (Equiv.Perm.sign tau) with heven | hodd
    · exact heven
    · exact (hnone ⟨tau, htau, hodd⟩).elim
  rw [Equiv.Perm.centralizer_le_alternating_iff] at hle
  rcases hsource with hpEven | hr2 | hfixed
  · have hpMem : p ∈ g.cycleType := by
      rw [hcycle]
      exact Multiset.mem_replicate.mpr ⟨Nat.ne_of_gt hr, rfl⟩
    have hpOdd := hle.1 p hpMem
    exact (Nat.not_even_iff_odd.mpr hpOdd) hpEven
  · have hcount := hle.2.2 p
    rw [hcycle, Multiset.count_replicate_self] at hcount
    omega
  · have hcard := hle.2.1
    have hsum : g.cycleType.sum = p * r := by
      rw [hcycle, Multiset.sum_replicate]
      simp only [nsmul_eq_mul]
      exact Nat.mul_comm r p
    rw [Fintype.card_fin, hsum] at hcard
    omega

/-- If the centralizer of a `p^r` permutation has no odd element, the only
possibility is one odd cycle with at most one fixed point. -/
theorem odd_single_cycle_exception_of_centralizer_le_alternating
    (g : Equiv.Perm (Fin n)) (hp : 2 ≤ p) (hr : 0 < r)
    (hcycle : g.cycleType = Multiset.replicate r p)
    (hle : Subgroup.centralizer ({g} : Set (Equiv.Perm (Fin n))) ≤
      alternatingGroup (Fin n)) :
    Odd p ∧ r = 1 ∧ n - p ≤ 1 := by
  rw [Equiv.Perm.centralizer_le_alternating_iff] at hle
  have hpMem : p ∈ g.cycleType := by
    rw [hcycle]
    exact Multiset.mem_replicate.mpr ⟨Nat.ne_of_gt hr, rfl⟩
  have hpOdd := hle.1 p hpMem
  have hcount := hle.2.2 p
  rw [hcycle, Multiset.count_replicate_self] at hcount
  have hr1 : r = 1 := by omega
  have hcard := hle.2.1
  have hsum : g.cycleType.sum = p * r := by
    rw [hcycle, Multiset.sum_replicate]
    simp only [nsmul_eq_mul]
    exact Nat.mul_comm r p
  rw [Fintype.card_fin, hsum, hr1, mul_one] at hcard
  exact ⟨hpOdd, hr1, by omega⟩

/-- Every transporter attached to cycle type `p^r` is parity-balanced, unless
`p` is odd, `r = 1`, and the permutation has at most one fixed point. -/
theorem transporter_parity_balanced_or_odd_single_cycle_exception
    (g : Equiv.Perm (Fin n)) (hp : 2 ≤ p) (hr : 0 < r)
    (hcycle : g.cycleType = Multiset.replicate r p) :
    (∀ b : Equiv.Perm (Fin n),
      2 * (evenConjugatingElements g b).card =
        (conjugatingElements g b).card) ∨
      (Odd p ∧ r = 1 ∧ n - p ≤ 1) := by
  classical
  by_cases hle : Subgroup.centralizer
      ({g} : Set (Equiv.Perm (Fin n))) ≤ alternatingGroup (Fin n)
  · exact Or.inr
      (odd_single_cycle_exception_of_centralizer_le_alternating
        g hp hr hcycle hle)
  · have hex : ∃ tau : Equiv.Perm (Fin n),
        tau ∈ Subgroup.centralizer ({g} : Set (Equiv.Perm (Fin n))) ∧
          Equiv.Perm.sign tau = -1 := by
      obtain ⟨tau, htau, htauNotAlt⟩ := SetLike.not_le_iff_exists.mp hle
      refine ⟨tau, htau, ?_⟩
      rw [Equiv.Perm.mem_alternatingGroup] at htauNotAlt
      exact (Int.units_eq_one_or (Equiv.Perm.sign tau)).resolve_left htauNotAlt
    obtain ⟨tau, htau, htauOdd⟩ := hex
    exact Or.inl fun b ↦
      two_mul_card_evenConjugatingElements_eq_card_conjugatingElements
        g b tau htau htauOdd

end Fin

end Kourovka213
