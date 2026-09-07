import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-!
# Arithmetic for a crude primitive-group order bound
-/

namespace Kourovka213

private theorem sq_succ_le_four_mul_two_pow (k : ℕ) :
    (k + 1) ^ 2 ≤ 4 * 2 ^ k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
      rcases k with _ | k
      · norm_num
      rcases k with _ | k
      · norm_num
      rcases k with _ | k
      · norm_num
      have ihprev := ih (k + 2) (by omega)
      have hsquare : (k + 4) ^ 2 ≤ 2 * (k + 3) ^ 2 := by
        calc
          (k + 4) ^ 2 ≤ (k + 4) ^ 2 + (k ^ 2 + 4 * k + 2) := Nat.le_add_right _ _
          _ = 2 * (k + 3) ^ 2 := by ring
      calc
        (k + 3 + 1) ^ 2 = (k + 4) ^ 2 := by ring
        _ ≤ 2 * (k + 3) ^ 2 := hsquare
        _ ≤ 2 * (4 * 2 ^ (k + 2)) := Nat.mul_le_mul_left 2 (by simpa using ihprev)
        _ = 4 * 2 ^ (k + 3) := by ring_nf

theorem sq_succ_log_two_le_eight_mul_pred (n : ℕ) (hn : 2 ≤ n) :
    (Nat.log 2 n + 1) ^ 2 ≤ 8 * (n - 1) := by
  have hn0 : n ≠ 0 := by omega
  calc
    (Nat.log 2 n + 1) ^ 2 ≤ 4 * 2 ^ Nat.log 2 n :=
      sq_succ_le_four_mul_two_pow _
    _ ≤ 4 * n := Nat.mul_le_mul_left 4 (Nat.pow_log_le_self 2 hn0)
    _ ≤ 8 * (n - 1) := by omega

/-- The deliberately loose constant `256` is enough for the primitive-order recursion. -/
theorem pow_succ_log_two_le_256_pow_pred (n : ℕ) (hn : 2 ≤ n) :
    n ^ (Nat.log 2 n + 1) ≤ 256 ^ (n - 1) := by
  have hn_upper : n ≤ 2 ^ (Nat.log 2 n + 1) :=
    (Nat.lt_pow_succ_log_self Nat.one_lt_two n).le
  calc
    n ^ (Nat.log 2 n + 1) ≤ (2 ^ (Nat.log 2 n + 1)) ^ (Nat.log 2 n + 1) :=
      Nat.pow_le_pow_left hn_upper _
    _ = 2 ^ ((Nat.log 2 n + 1) ^ 2) := by rw [← pow_mul]; ring_nf
    _ ≤ 2 ^ (8 * (n - 1)) :=
      Nat.pow_le_pow_right (by norm_num) (sq_succ_log_two_le_eight_mul_pred n hn)
    _ = 256 ^ (n - 1) := by norm_num [pow_mul]

end Kourovka213
