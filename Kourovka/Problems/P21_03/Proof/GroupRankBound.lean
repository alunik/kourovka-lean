import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.Rank

/-!
# A logarithmic generator bound for finite groups

The crude primitive-soluble order estimate used in this project only needs the elementary fact
that a finite group has a generating set of size at most `log 2 |G|`.  We prove it here from
Lagrange's theorem: adjoining an element outside a subgroup at least doubles its order.
-/

open scoped Pointwise

namespace Kourovka213

theorem two_mul_natCard_le_of_subgroup_lt {G : Type*} [Group G]
    {H K : Subgroup G} [Finite K] (hHK : H < K) :
    2 * Nat.card H ≤ Nat.card K := by
  have hcard := Subgroup.card_lt_of_lt hHK
  obtain ⟨c, hc⟩ := Subgroup.card_dvd_of_le hHK.le
  have hc0 : c ≠ 0 := by
    intro h
    subst c
    simp at hc
    exact Nat.card_pos.ne' hc
  have hc1 : c ≠ 1 := by
    intro h
    subst c
    simp at hc
    omega
  have htwo : 2 ≤ c := (Nat.two_le_iff c).2 ⟨hc0, hc1⟩
  calc
    2 * Nat.card H = Nat.card H * 2 := Nat.mul_comm _ _
    _ ≤ Nat.card H * c := Nat.mul_le_mul_left _ htwo
    _ = Nat.card K := hc.symm

/-- An irredundant finite generating family forces the generated subgroup to have at least
`2 ^ |S|` elements. -/
theorem two_pow_card_le_natCard_closure {G : Type*} [Group G] [Finite G] [DecidableEq G]
    (S : Finset G)
    (hirr : ∀ x ∈ S, x ∉ Subgroup.closure (S.erase x : Set G)) :
    2 ^ S.card ≤ Nat.card (Subgroup.closure (S : Set G)) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
      have hirrS : ∀ x ∈ S, x ∉ Subgroup.closure (S.erase x : Set G) := by
        intro x hxS hx
        apply hirr x (Finset.mem_insert_of_mem hxS)
        exact (Subgroup.closure_mono (by
          intro y hy
          change y ∈ S.erase x at hy
          change y ∈ (insert a S).erase x
          exact Finset.mem_erase.mpr
            ⟨(Finset.mem_erase.mp hy).1,
              Finset.mem_insert_of_mem (Finset.mem_erase.mp hy).2⟩)) hx
      have hi := ih hirrS
      have ha_closure : a ∉ Subgroup.closure (S : Set G) := by
        have h := hirr a (Finset.mem_insert_self a S)
        simpa [Finset.erase_insert ha] using h
      have hclosure_lt :
          Subgroup.closure (S : Set G) <
            Subgroup.closure ((↑(insert a S) : Set G)) := by
        refine lt_of_le_of_ne (Subgroup.closure_mono ?_) ?_
        · exact_mod_cast Finset.subset_insert a S
        · intro heq
          apply ha_closure
          rw [heq]
          exact Subgroup.subset_closure (by simp)
      have hdouble := two_mul_natCard_le_of_subgroup_lt hclosure_lt
      calc
        2 ^ (insert a S).card = 2 * 2 ^ S.card := by simp [ha, pow_succ, mul_comm]
        _ ≤ 2 * Nat.card (Subgroup.closure (S : Set G)) := Nat.mul_le_mul_left 2 hi
        _ ≤ Nat.card (Subgroup.closure ((↑(insert a S) : Set G))) := hdouble

/-- The minimum number of generators of a finite group is at most `log 2 |G|`. -/
theorem group_rank_le_log_two_natCard (G : Type*) [Group G] [Finite G] :
    Group.rank G ≤ Nat.log 2 (Nat.card G) := by
  classical
  obtain ⟨S, hScard, hSgen⟩ := Group.rank_spec G
  have hirr : ∀ x ∈ S, x ∉ Subgroup.closure (S.erase x : Set G) := by
    intro x hxS hxclosure
    have herase : Subgroup.closure (S.erase x : Set G) = ⊤ := by
      apply top_unique
      rw [← hSgen]
      rw [Subgroup.closure_le]
      intro y hy
      by_cases hyx : y = x
      · simpa [hyx] using hxclosure
      · exact Subgroup.subset_closure (by
          simpa [Finset.mem_erase, hyx] using hy)
    have hrank := Group.rank_le herase
    have herasecard := Finset.card_erase_of_mem hxS
    have hrankpos : 0 < Group.rank G := by
      rw [← hScard]
      exact Finset.card_pos.mpr ⟨x, hxS⟩
    rw [herasecard, hScard] at hrank
    omega
  apply Nat.le_log_of_pow_le Nat.one_lt_two
  rw [← hScard]
  simpa [hSgen] using two_pow_card_le_natCard_closure S hirr

end Kourovka213
