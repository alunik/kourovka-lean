import Mathlib.GroupTheory.Perm.Centralizer
import Mathlib.Algebra.Order.BigOperators.Group.Multiset

/-!
# Cycle-type bounds for permutation conjugacy classes

This file isolates two elementary estimates used in bounding the non-fixed
part of a permutation centralizer.  They are stated first for multisets and
then specialized to permutation cycle types.
-/

open scoped BigOperators

namespace Kourovka213

/-- If every entry of a multiset is at least two, twice its cardinality is at
most its sum. -/
theorem two_mul_card_le_sum_of_two_le
    (s : Multiset ℕ) (hs : ∀ a ∈ s, 2 ≤ a) :
    2 * s.card ≤ s.sum := by
  simpa [Nat.nsmul_eq_mul, Nat.mul_comm] using
    (Multiset.card_nsmul_le_sum (s := s) (a := 2) hs)

private theorem weighted_count_le_sum (s : Multiset ℕ) {a : ℕ}
    (ha : a ∈ s.toFinset) :
    a * s.count a ≤ s.sum := by
  have hsingle : s.count a * a ≤
      ∑ b ∈ s.toFinset, s.count b * b := by
    exact Finset.single_le_sum (f := fun b ↦ s.count b * b)
      (fun _ _ ↦ Nat.zero_le _) ha
  have hsum : (∑ b ∈ s.toFinset, s.count b * b) = s.sum := by
    simpa [Nat.nsmul_eq_mul] using
      (Finset.sum_multiset_map_count s id).symm
  calc
    a * s.count a = s.count a * a := Nat.mul_comm _ _
    _ ≤ ∑ b ∈ s.toFinset, s.count b * b := hsingle
    _ = s.sum := hsum

/-- The product of cycle lengths, including the factorial correction for
repeated lengths, is bounded by `sum ^ card`.  This is the exact elementary
inequality needed for the non-fixed part of a permutation centralizer. -/
theorem multiset_prod_mul_count_factorial_le_sum_pow_card (s : Multiset ℕ) :
    s.prod * (∏ a ∈ s.toFinset, Nat.factorial (s.count a)) ≤ s.sum ^ s.card := by
  classical
  calc
    s.prod * (∏ a ∈ s.toFinset, Nat.factorial (s.count a)) =
        (∏ a ∈ s.toFinset, a ^ s.count a) *
          (∏ a ∈ s.toFinset, Nat.factorial (s.count a)) := by
      rw [Finset.prod_multiset_count]
    _ = ∏ a ∈ s.toFinset, a ^ s.count a * Nat.factorial (s.count a) := by
      rw [Finset.prod_mul_distrib]
    _ ≤ ∏ a ∈ s.toFinset, s.sum ^ s.count a := by
      apply Finset.prod_le_prod
      · exact fun _ _ ↦ Nat.zero_le _
      · intro a ha
        calc
          a ^ s.count a * Nat.factorial (s.count a) ≤
              a ^ s.count a * (s.count a) ^ s.count a :=
            Nat.mul_le_mul_left _ (Nat.factorial_le_pow _)
          _ = (a * s.count a) ^ s.count a := by rw [Nat.mul_pow]
          _ ≤ s.sum ^ s.count a :=
            Nat.pow_le_pow_left (weighted_count_le_sum s ha) _
    _ = s.sum ^ (∑ a ∈ s.toFinset, s.count a) := by
      rw [Finset.prod_pow_eq_pow_sum]
    _ = s.sum ^ s.card := by rw [Multiset.toFinset_sum_count_eq]

variable {n : ℕ}

/-- Each nontrivial cycle has length at least two, so a permutation has at
most half as many nontrivial cycles as moved points. -/
theorem two_mul_cycleType_card_le_support_card (g : Equiv.Perm (Fin n)) :
    2 * g.cycleType.card ≤ g.support.card := by
  rw [← Equiv.Perm.sum_cycleType]
  exact two_mul_card_le_sum_of_two_le g.cycleType
    (fun _ h ↦ Equiv.Perm.two_le_of_mem_cycleType h)

theorem cycleType_card_le_support_card_div_two (g : Equiv.Perm (Fin n)) :
    g.cycleType.card ≤ g.support.card / 2 := by
  apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).mpr
  simpa [Nat.mul_comm] using two_mul_cycleType_card_le_support_card g

/-- The non-fixed centralizer factor is bounded by the number of moved points
to the number of nontrivial cycles. -/
theorem cycleType_prod_mul_count_factorial_le_support_pow_card
    (g : Equiv.Perm (Fin n)) :
    g.cycleType.prod *
        (∏ a ∈ g.cycleType.toFinset, Nat.factorial (g.cycleType.count a)) ≤
      g.support.card ^ g.cycleType.card := by
  simpa [Equiv.Perm.sum_cycleType] using
    multiset_prod_mul_count_factorial_le_sum_pow_card g.cycleType

/-- The same estimate with the number of cycles eliminated. -/
theorem cycleType_prod_mul_count_factorial_le_support_pow_half
    (g : Equiv.Perm (Fin n)) :
    g.cycleType.prod *
        (∏ a ∈ g.cycleType.toFinset, Nat.factorial (g.cycleType.count a)) ≤
      g.support.card ^ (g.support.card / 2) := by
  by_cases hg : g = 1
  · simp [hg]
  · exact (cycleType_prod_mul_count_factorial_le_support_pow_card g).trans
      (Nat.pow_le_pow_right
        (Nat.pos_of_ne_zero (Equiv.Perm.card_support_eq_zero.not.mpr hg))
        (cycleType_card_le_support_card_div_two g))

/-- A direct lower bound for the size of a conjugacy class.  It keeps the
falling-factorial contribution exact and replaces only the non-fixed
centralizer factor by the preceding power bound. -/
theorem factorial_div_fixed_mul_support_pow_card_le_card_isConj
    (g : Equiv.Perm (Fin n)) :
    n.factorial /
        ((n - g.support.card).factorial *
          g.support.card ^ g.cycleType.card) ≤
      Nat.card {h : Equiv.Perm (Fin n) | IsConj g h} := by
  let exactDenominator : ℕ :=
    (n - g.cycleType.sum).factorial * g.cycleType.prod *
      (∏ a ∈ g.cycleType.toFinset, Nat.factorial (g.cycleType.count a))
  have hexact_pos : 0 < exactDenominator := by
    simp only [exactDenominator]
    have hcentral :
        Nat.card (Subgroup.centralizer {g}) =
          (n - g.cycleType.sum).factorial * g.cycleType.prod *
            (∏ a ∈ g.cycleType.toFinset,
              Nat.factorial (g.cycleType.count a)) := by
      simpa only [Fintype.card_fin] using Equiv.Perm.nat_card_centralizer g
    rw [← hcentral]
    exact Nat.card_pos
  have hdenominator : exactDenominator ≤
      (n - g.support.card).factorial *
        g.support.card ^ g.cycleType.card := by
    simp only [exactDenominator]
    rw [Equiv.Perm.sum_cycleType]
    simpa [Nat.mul_assoc] using
      Nat.mul_le_mul_left (n - g.support.card).factorial
        (cycleType_prod_mul_count_factorial_le_support_pow_card g)
  calc
    n.factorial /
          ((n - g.support.card).factorial *
            g.support.card ^ g.cycleType.card) ≤
        n.factorial / exactDenominator :=
      Nat.div_le_div_left hdenominator hexact_pos
    _ = Nat.card {h : Equiv.Perm (Fin n) | IsConj g h} := by
      rw [Equiv.Perm.card_isConj_eq]
      simp only [exactDenominator, Equiv.Perm.sum_cycleType, Fintype.card_fin]

/-- A cycle-count-free conjugacy-class lower bound. -/
theorem factorial_div_fixed_mul_support_pow_half_le_card_isConj
    (g : Equiv.Perm (Fin n)) :
    n.factorial /
        ((n - g.support.card).factorial *
          g.support.card ^ (g.support.card / 2)) ≤
      Nat.card {h : Equiv.Perm (Fin n) | IsConj g h} := by
  by_cases hg : g = 1
  · subst g
    rw [Equiv.Perm.card_isConj_eq]
    simp
  · have hspos : 0 < g.support.card :=
      Nat.pos_of_ne_zero (Equiv.Perm.card_support_eq_zero.not.mpr hg)
    have hpow : g.support.card ^ g.cycleType.card ≤
        g.support.card ^ (g.support.card / 2) :=
      Nat.pow_le_pow_right hspos (cycleType_card_le_support_card_div_two g)
    have hden :
        (n - g.support.card).factorial *
            g.support.card ^ g.cycleType.card ≤
          (n - g.support.card).factorial *
            g.support.card ^ (g.support.card / 2) :=
      Nat.mul_le_mul_left _ hpow
    calc
      n.factorial /
            ((n - g.support.card).factorial *
              g.support.card ^ (g.support.card / 2)) ≤
          n.factorial /
            ((n - g.support.card).factorial *
              g.support.card ^ g.cycleType.card) :=
        Nat.div_le_div_left hden
          (Nat.mul_pos (Nat.factorial_pos _) (Nat.pow_pos hspos))
      _ ≤ Nat.card {h : Equiv.Perm (Fin n) | IsConj g h} :=
        factorial_div_fixed_mul_support_pow_card_le_card_isConj g

end Kourovka213
