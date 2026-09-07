import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Factorial.BigOperators

/-!
# Arithmetic for finite atom-set counts

The recursive support encoding produces an unordered set of `k` atoms of total
weight `s`, with every atom of weight at least two.  These elementary inequalities
absorb the binomial choice of locations into the fixed exponential constant while
retaining the required power of the ambient degree.
-/

namespace Kourovka213

/-- If `k ≤ s/2`, the loss from replacing a falling factorial by `s^k`
is bounded by a fixed exponential in `s`. -/
theorem pow_le_four_pow_mul_factorial_of_two_mul_le
    (s k : ℕ) (hk : 2 * k ≤ s) :
    s ^ k ≤ 4 ^ s * k.factorial := by
  have hbase : s ≤ 2 * (s + 1 - k) := by omega
  have hfall : (s + 1 - k) ^ k ≤ s.descFactorial k :=
    Nat.pow_sub_le_descFactorial s k
  have hchoose : s.choose k ≤ 2 ^ s := Nat.choose_le_two_pow s k
  have hk_s : k ≤ s := by omega
  calc
    s ^ k ≤ (2 * (s + 1 - k)) ^ k := pow_le_pow_left' hbase k
    _ = 2 ^ k * (s + 1 - k) ^ k := by rw [Nat.mul_pow]
    _ ≤ 2 ^ k * s.descFactorial k := Nat.mul_le_mul_left _ hfall
    _ = 2 ^ k * (k.factorial * s.choose k) := by
      rw [Nat.descFactorial_eq_factorial_mul_choose]
    _ ≤ 2 ^ k * (k.factorial * 2 ^ s) := by
      exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hchoose)
    _ = 2 ^ (k + s) * k.factorial := by
      rw [pow_add]
      ac_rfl
    _ ≤ 2 ^ (s + s) * k.factorial := by
      exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) (by omega))
    _ = 4 ^ s * k.factorial := by
      rw [pow_add, ← Nat.mul_pow]

/-- Choosing `k` unordered locations among at most `n`, then clearing the
support denominator, costs only `4^s` while preserving the target `n^q`.
This is the numerical form used for both ordinary atoms and marked bad atoms. -/
theorem choose_mul_support_pow_le_four_pow_mul_degree_pow
    (n s k q : ℕ) (hkn : k ≤ n) (hks : 2 * k ≤ s)
    (hkq : k ≤ q) (hqn : q ≤ s) (hsn : s ≤ n) :
    n.choose k * s ^ q ≤ 4 ^ s * n ^ q := by
  have hchooseFactorial : n.choose k * k.factorial ≤ n ^ k := by
    rw [Nat.mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose]
    exact n.descFactorial_le_pow k
  have hsPow := pow_le_four_pow_mul_factorial_of_two_mul_le s k hks
  have hsq : s ^ (q - k) ≤ n ^ (q - k) := pow_le_pow_left' hsn _
  have hq : k + (q - k) = q := Nat.add_sub_of_le hkq
  calc
    n.choose k * s ^ q = n.choose k * (s ^ k * s ^ (q - k)) := by
      rw [← pow_add, hq]
    _ ≤ n.choose k * ((4 ^ s * k.factorial) * s ^ (q - k)) := by
      exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hsPow)
    _ = 4 ^ s * (n.choose k * k.factorial) * s ^ (q - k) := by ac_rfl
    _ ≤ 4 ^ s * n ^ k * s ^ (q - k) := by
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hchooseFactorial)
    _ ≤ 4 ^ s * n ^ k * n ^ (q - k) := by
      exact Nat.mul_le_mul_left _ hsq
    _ = 4 ^ s * n ^ q := by rw [mul_assoc, ← pow_add, hq]

end Kourovka213
