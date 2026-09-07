import Kourovka.Problems.P21_03.Proof.Basic
import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# Reduction of a nontrivial intersection to prime-order rows

Every nontrivial finite subgroup contains an element of prime order.  For a
permutation, prime order forces cycle type `p^r`, hence support `p*r`.  This
is the group-theoretic reduction which makes the prime-indexed effective
majorant exhaustive.
-/

open Subgroup

namespace Kourovka213

variable {n : ℕ}

/-- A nontrivial intersection of two permutation subgroups contains an
element of prime order. -/
theorem exists_prime_order_mem_of_not_disjoint
    (H K : Subgroup (Sym n)) (hHK : ¬ Disjoint H K) :
    ∃ p : ℕ, p.Prime ∧ ∃ g : Sym n,
      g ∈ H ∧ g ∈ K ∧ orderOf g = p := by
  let L : Subgroup (Sym n) := H ⊓ K
  have hL : L ≠ ⊥ := by
    intro hbot
    apply hHK
    rw [disjoint_iff]
    exact hbot
  have hcard : Nat.card L ≠ 1 := by
    intro hcard
    exact hL (Subgroup.eq_bot_of_card_eq L hcard)
  obtain ⟨p, hp, hpCard⟩ := Nat.exists_prime_and_dvd hcard
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hgOrder⟩ := exists_prime_orderOf_dvd_card' (G := L) p hpCard
  refine ⟨p, hp, g.1, g.2.1, g.2.2, ?_⟩
  exact (Subgroup.orderOf_coe g).trans hgOrder

/-- Prime-order permutations have a positive number of equal prime cycles,
and their support is exactly the prime times that cycle count. -/
theorem prime_order_cycle_support
    (g : Sym n) (p : ℕ) (hp : p.Prime) (hg : orderOf g = p) :
    ∃ r : ℕ, 0 < r ∧ g.cycleType = Multiset.replicate r p ∧
      g.support.card = p * r := by
  have horderPrime : (orderOf g).Prime := hg ▸ hp
  obtain ⟨k, hcycle⟩ := Equiv.Perm.cycleType_prime_order horderPrime
  refine ⟨k + 1, by omega, ?_, ?_⟩
  · simpa [hg] using hcycle
  · calc
      g.support.card = g.cycleType.sum := g.sum_cycleType.symm
      _ = (Multiset.replicate (k + 1) p).sum := by rw [hcycle, hg]
      _ = p * (k + 1) := by
        simp only [Multiset.sum_replicate, nsmul_eq_mul]
        simp [Nat.add_mul, Nat.mul_add, Nat.mul_comm]

/-- Complete prime-row witness extracted from every nontrivial intersection. -/
theorem exists_prime_cycle_row_mem_of_not_disjoint
    (H K : Subgroup (Sym n)) (hHK : ¬ Disjoint H K) :
    ∃ p r : ℕ, p.Prime ∧ 0 < r ∧ ∃ g : Sym n,
      g ∈ H ∧ g ∈ K ∧ orderOf g = p ∧
        g.cycleType = Multiset.replicate r p ∧
        g.support.card = p * r := by
  obtain ⟨p, hp, g, hgH, hgK, hgOrder⟩ :=
    exists_prime_order_mem_of_not_disjoint H K hHK
  obtain ⟨r, hr, hcycle, hsupport⟩ :=
    prime_order_cycle_support g p hp hgOrder
  exact ⟨p, r, hp, hr, g, hgH, hgK, hgOrder, hcycle, hsupport⟩

end Kourovka213
