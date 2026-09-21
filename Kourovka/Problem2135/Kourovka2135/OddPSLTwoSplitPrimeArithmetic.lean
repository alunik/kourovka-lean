import Mathlib.Data.Nat.Factors
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic

/-! Elementary arithmetic locating an odd split-torus prime.

An integer which is not a power of two has an odd prime divisor. Moreover,
3^f-1 has such a divisor for every odd f at least three: 3^f is three modulo
eight, so 3^f-1 is not divisible by four and is greater than two. No list of
primes or finite-field classification is used.
-/

set_option autoImplicit false
namespace Kourovka2135.OddPSLTwoSplitPrimeArithmetic

theorem exists_odd_prime_dvd_of_not_two_pow {n : ℕ}
    (hnot : ¬ ∃ k : ℕ, n = 2 ^ k) :
    ∃ r : ℕ, r.Prime ∧ Odd r ∧ r ∣ n := by
  obtain h | ⟨r, hr, hd, ho⟩ := Nat.eq_two_pow_or_exists_odd_prime_and_dvd n
  · exact (hnot h).elim
  · exact ⟨r, hr, ho, hd⟩

/-- In particular this applies to every prime q whose q-1 is not a power
of two; the arithmetic statement itself needs no primality premise. -/
theorem exists_odd_prime_dvd_sub_one_of_not_two_pow {q : ℕ}
    (hnot : ¬ ∃ k : ℕ, q - 1 = 2 ^ k) :
    ∃ r : ℕ, r.Prime ∧ Odd r ∧ r ∣ q - 1 :=
  exists_odd_prime_dvd_of_not_two_pow hnot

theorem three_pow_mod_eight {f : ℕ} (hf : Odd f) : 3 ^ f % 8 = 3 := by
  obtain ⟨k, rfl⟩ := hf
  have h : Nat.ModEq 8 (3 ^ 2) 1 := by decide
  have hp := h.pow k
  change (3 ^ 2) ^ k % 8 = 1 ^ k % 8 at hp
  rw [one_pow] at hp
  rw [pow_add, pow_mul, pow_one, Nat.mul_mod, hp]
  norm_num

theorem seventeen_le_three_pow {f : ℕ} (hf : 3 ≤ f) : 17 ≤ 3 ^ f := by
  have hp := Nat.pow_le_pow_right (by decide : 0 < 3) hf
  norm_num at hp
  omega

theorem exists_odd_prime_dvd_three_pow_sub_one {f : ℕ}
    (hf : Odd f) (hsize : 3 ≤ f) :
    ∃ r : ℕ, r.Prime ∧ Odd r ∧ r ∣ 3 ^ f - 1 := by
  have hbound := seventeen_le_three_pow hsize
  obtain hd | ⟨r, hr, hd, ho⟩ :=
    Nat.four_dvd_or_exists_odd_prime_and_dvd_of_two_lt (show 2 < 3 ^ f - 1 by omega)
  · have hm := three_pow_mod_eight hf
    have hz := Nat.mod_eq_zero_of_dvd hd
    omega
  · exact ⟨r, hr, ho, hd⟩

/-- The odd-prime exponent parameters in the minimal-simple list satisfy
the stronger preceding statement. -/
theorem exists_odd_prime_dvd_three_pow_sub_one_of_prime {f : ℕ}
    (hprime : f.Prime) (hf : Odd f) :
    ∃ r : ℕ, r.Prime ∧ Odd r ∧ r ∣ 3 ^ f - 1 := by
  apply exists_odd_prime_dvd_three_pow_sub_one hf
  have htwo := hprime.two_le
  have hmod := Nat.odd_iff.mp hf
  omega

end Kourovka2135.OddPSLTwoSplitPrimeArithmetic
