import Mathlib.Data.Nat.Choose.Sum

/-!
# Finite Bonferroni inequalities

Mathlib has exact inclusion--exclusion but (at the pinned revision) does not contain the
upper and lower inequalities obtained by truncating it.  For the configuration model it is
more convenient to formulate those inequalities directly in terms of the binomial moments
of an integer-valued collision count.
-/

open scoped BigOperators

namespace Kourovka213

/-- The inclusion--exclusion polynomial truncated after degree `k`, evaluated at `m`. -/
def truncatedBinomial (k m : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (k + 1), (-1 : ℤ) ^ j * m.choose j

/-- The indicator that a natural number vanishes, valued in the integers. -/
def zeroIndicator (m : ℕ) : ℤ := if m = 0 then 1 else 0

@[simp]
theorem truncatedBinomial_zero (k : ℕ) : truncatedBinomial k 0 = 1 := by
  induction k with
  | zero => simp [truncatedBinomial]
  | succ k ih =>
      simp only [truncatedBinomial, Nat.succ_eq_add_one] at ih ⊢
      rw [Finset.sum_range_succ, ih]
      simp [Nat.choose_zero_succ]

theorem truncatedBinomial_succ (k m : ℕ) :
    truncatedBinomial k (m + 1) = (-1 : ℤ) ^ k * m.choose k := by
  exact Int.alternating_sum_range_choose_eq_choose

theorem zeroIndicator_le_truncatedBinomial_even (r m : ℕ) :
    zeroIndicator m ≤ truncatedBinomial (2 * r) m := by
  cases m with
  | zero => simp [zeroIndicator]
  | succ m =>
      rw [zeroIndicator, if_neg (Nat.succ_ne_zero _), truncatedBinomial_succ]
      simp [pow_mul]

theorem truncatedBinomial_odd_le_zeroIndicator (r m : ℕ) :
    truncatedBinomial (2 * r + 1) m ≤ zeroIndicator m := by
  cases m with
  | zero => simp [zeroIndicator]
  | succ m =>
      rw [zeroIndicator, if_neg (Nat.succ_ne_zero _), truncatedBinomial_succ]
      simp [pow_succ, pow_mul]

section Finite

variable {Omega : Type*} [Fintype Omega]

/-- Number of outcomes at which the collision count `Z` is zero. -/
def zeroCount (Z : Omega → ℕ) : ℕ :=
  (Finset.univ.filter fun w => Z w = 0).card

/-- The `j`th binomial moment of a collision count, without probability normalization. -/
def binomialMoment (Z : Omega → ℕ) (j : ℕ) : ℤ :=
  ∑ w : Omega, (Z w).choose j

/-- An even Bonferroni truncation is an upper bound for the zero count. -/
theorem zeroCount_le_evenBonferroni (Z : Omega → ℕ) (r : ℕ) :
    (zeroCount Z : ℤ) ≤
      ∑ j ∈ Finset.range (2 * r + 1), (-1 : ℤ) ^ j * binomialMoment Z j := by
  classical
  calc
    (zeroCount Z : ℤ) = ∑ w : Omega, zeroIndicator (Z w) := by
      simp [zeroCount, zeroIndicator]
    _ ≤ ∑ w : Omega, truncatedBinomial (2 * r) (Z w) :=
      Finset.sum_le_sum fun w _ => zeroIndicator_le_truncatedBinomial_even r (Z w)
    _ = ∑ j ∈ Finset.range (2 * r + 1), (-1 : ℤ) ^ j * binomialMoment Z j := by
      simp only [truncatedBinomial, binomialMoment, Finset.mul_sum]
      rw [Finset.sum_comm]

/-- An odd Bonferroni truncation is a lower bound for the zero count. -/
theorem oddBonferroni_le_zeroCount (Z : Omega → ℕ) (r : ℕ) :
    (∑ j ∈ Finset.range (2 * r + 2), (-1 : ℤ) ^ j * binomialMoment Z j) ≤
      (zeroCount Z : ℤ) := by
  classical
  calc
    (∑ j ∈ Finset.range (2 * r + 2), (-1 : ℤ) ^ j * binomialMoment Z j) =
        ∑ w : Omega, truncatedBinomial (2 * r + 1) (Z w) := by
      simp only [truncatedBinomial, binomialMoment, Finset.mul_sum]
      rw [Finset.sum_comm]
    _ ≤ ∑ w : Omega, zeroIndicator (Z w) :=
      Finset.sum_le_sum fun w _ => truncatedBinomial_odd_le_zeroIndicator r (Z w)
    _ = (zeroCount Z : ℤ) := by
      simp [zeroCount, zeroIndicator]

end Finite

end Kourovka213
