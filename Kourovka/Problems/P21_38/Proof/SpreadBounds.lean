import Kourovka.Problems.P21_38.Proof.Spread

/-!
# Monotonicity and exact spread

The ordinary spread conditions decrease with the number of prescribed elements.
Consequently, the definition of exact spread one in `Spread` says precisely that
the natural numbers satisfying the spread condition are zero and one.
-/

namespace Kourovka.P21_38

variable {G : Type*} [Group G]

/-- A common companion for every `n`-tuple gives one for every shorter tuple.

A nonempty shorter tuple is padded by repeating its first element.  The empty
tuple is treated separately, so no nontriviality assumption on `G` is needed. -/
theorem HasSpreadAtLeast.mono {m n : ℕ} (h : HasSpreadAtLeast G n)
    (hmn : m ≤ n) : HasSpreadAtLeast G m := by
  cases m with
  | zero => exact hasSpreadAtLeast_zero
  | succ m =>
    intro x hx
    let extended : Fin n → G := fun i =>
      if hi : i.val < m + 1 then x ⟨i.val, hi⟩ else x 0
    have hextended : ∀ i, extended i ≠ 1 := by
      intro i
      dsimp [extended]
      split <;> exact hx _
    obtain ⟨y, hy⟩ := h extended hextended
    refine ⟨y, fun i => ?_⟩
    have hi : i.val < n := lt_of_lt_of_le i.isLt hmn
    simpa only [extended, dite_eq_left i.isLt] using hy ⟨i.val, hi⟩

/-- Exact spread one means that one is the greatest natural number satisfying
the ordinary spread condition. -/
theorem hasSpreadExactlyOne_iff_forall :
    HasSpreadExactlyOne G ↔ ∀ k, HasSpreadAtLeast G k ↔ k ≤ 1 := by
  constructor
  · rintro ⟨h₁, h₂⟩ k
    constructor
    · intro hk
      apply Nat.le_of_lt_succ
      apply Nat.lt_of_not_ge
      intro htwo
      exact h₂ (hk.mono htwo)
    · exact h₁.mono
  · intro h
    refine ⟨(h 1).mpr le_rfl, ?_⟩
    intro htwo
    exact Nat.not_succ_le_self 1 ((h 2).mp htwo)

end Kourovka.P21_38
