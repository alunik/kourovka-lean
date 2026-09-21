import Kourovka2135.ClassTwoPowers
import Mathlib.Data.Nat.Choose.Basic

/-! The class-two binomial identity and the odd-prime power homomorphism. -/

set_option autoImplicit false
universe u
namespace Kourovka2135
variable {G : Type u} [Group G]

theorem mul_pow_of_central_paperCommutator (x y : G)
    (hc : paperCommutator y x ∈ Subgroup.center G) (n : ℕ) :
    (x * y) ^ n = x ^ n * y ^ n * paperCommutator y x ^ (n.choose 2) := by
  let c := paperCommutator y x
  have hcomm (z : G) : Commute c z :=
    (show Commute z c from Subgroup.mem_center_iff.mp hc z).symm
  have hrel (m : ℕ) : y ^ m * x = x * y ^ m * c ^ m := by
    calc
      y ^ m * x = x * y ^ m * paperCommutator (y ^ m) x := by
        simp only [paperCommutator, mul_assoc, mul_inv_cancel_left]
      _ = x * y ^ m * c ^ m := by
        rw [paperCommutator_pow_left_of_commute y x (hcomm y)]
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      (x * y) ^ (n + 1) = (x ^ n * y ^ n * c ^ (n.choose 2)) * (x * y) := by
        rw [pow_succ, ih]
      _ = x ^ n * y ^ n * (x * y) * c ^ (n.choose 2) := by
        rw [mul_assoc (x ^ n * y ^ n), ((hcomm (x * y)).pow_left _).eq]
        simp only [mul_assoc]
      _ = x ^ n * (y ^ n * x) * y * c ^ (n.choose 2) := by group
      _ = x ^ n * (x * y ^ n * c ^ n) * y * c ^ (n.choose 2) := by rw [hrel]
      _ = x ^ (n + 1) * y ^ (n + 1) * c ^ n * c ^ (n.choose 2) := by
        calc
          x ^ n * (x * y ^ n * c ^ n) * y * c ^ n.choose 2 =
              x ^ n * x * y ^ n * (c ^ n * y) * c ^ n.choose 2 := by group
          _ = x ^ n * x * y ^ n * (y * c ^ n) * c ^ n.choose 2 := by
            rw [((hcomm y).pow_left n).eq]
          _ = x ^ (n + 1) * y ^ (n + 1) * c ^ n * c ^ n.choose 2 := by group
      _ = x ^ (n + 1) * y ^ (n + 1) * c ^ ((n + 1).choose 2) := by
        rw [Nat.choose_succ_succ, Nat.choose_one_right, pow_add c]
        simp only [mul_assoc]

theorem mul_pow_prime_of_central_commutator {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (x y : G) (hc : paperCommutator y x ∈ Subgroup.center G)
    (hpow : paperCommutator y x ^ p = 1) : (x * y) ^ p = x ^ p * y ^ p := by
  have hpodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left hodd
  have heven : 2 ∣ p - 1 := by omega
  have hdvd : p ∣ p.choose 2 := by
    rw [Nat.choose_two_right, Nat.mul_div_assoc p heven]
    exact dvd_mul_right _ _
  obtain ⟨k, hk⟩ := hdvd
  rw [mul_pow_of_central_paperCommutator x y hc, hk, pow_mul, hpow, one_pow, mul_one]

end Kourovka2135
