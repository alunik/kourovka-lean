import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Subgroup.Center

/-! Uniqueness of prime-to-p lifts across an actual central p-group kernel.

The common-exponent form requires neither finite ambient groups nor primality of
p. Centrality makes two lifts of one element commute; their difference lies in
the kernel, where an exponent coprime to p can kill only the identity.
-/

set_option autoImplicit false

namespace Kourovka2135.CentralPGroupOddLift

universe u v
variable {H : Type u} {G : Type v} [Group H] [Group G]
variable (pi : H →* G)

/-- Two elements with the same image commute when the actual kernel is central. -/
theorem commute_of_map_eq (hcentral : pi.ker ≤ Subgroup.center H)
    {x y : H} (hmap : pi x = pi y) : Commute x y := by
  have hmem : x * y⁻¹ ∈ pi.ker := by
    change pi (x * y⁻¹) = 1
    rw [map_mul, map_inv, hmap, mul_inv_cancel]
  have hzy : Commute (x * y⁻¹) y :=
    (Subgroup.mem_center_iff.mp (hcentral hmem) y).symm
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using
    hzy.mul_left (Commute.refl y)

/-- A prime-to-p power distinguishes lifts through a central p-group kernel. -/
theorem eq_of_pow_eq_of_coprime {p m : ℕ}
    (hcentral : pi.ker ≤ Subgroup.center H) (hker : IsPGroup p pi.ker)
    (hm : Nat.Coprime p m) {x y : H} (hmap : pi x = pi y)
    (hpow : x ^ m = y ^ m) : x = y := by
  have hmem : x * y⁻¹ ∈ pi.ker := by
    change pi (x * y⁻¹) = 1
    rw [map_mul, map_inv, hmap, mul_inv_cancel]
  let z : pi.ker := ⟨x * y⁻¹, hmem⟩
  have hzpow : z ^ m = 1 := by
    apply Subtype.ext
    change (x * y⁻¹) ^ m = 1
    rw [(commute_of_map_eq pi hcentral hmap).inv_right.mul_pow,
      inv_pow, hpow, mul_inv_cancel]
  have hz : z = 1 := orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes (hker.orderOf_coprime hm z)
      dvd_rfl (orderOf_dvd_of_pow_eq_one hzpow))
  apply mul_inv_eq_one.mp
  exact congrArg (fun a : pi.ker => (a : H)) hz

/-- Two lifts killed by a common exponent coprime to p coincide. -/
theorem eq_of_common_exponent {p m : ℕ}
    (hcentral : pi.ker ≤ Subgroup.center H) (hker : IsPGroup p pi.ker)
    (hm : Nat.Coprime p m) {x y : H} (hmap : pi x = pi y)
    (hx : x ^ m = 1) (hy : y ^ m = 1) : x = y :=
  eq_of_pow_eq_of_coprime pi hcentral hker hm hmap (hx.trans hy.symm)

/-- Prime-to-p element orders give uniqueness without a finite-group premise. -/
theorem eq_of_coprime_orderOf {p : ℕ}
    (hcentral : pi.ker ≤ Subgroup.center H) (hker : IsPGroup p pi.ker)
    {x y : H} (hmap : pi x = pi y)
    (hx : Nat.Coprime p (orderOf x)) (hy : Nat.Coprime p (orderOf y)) : x = y := by
  apply eq_of_common_exponent pi hcentral hker (hx.mul_right hy) hmap
  · rw [pow_mul, pow_orderOf_eq_one, one_pow]
  · rw [Nat.mul_comm (orderOf x), pow_mul, pow_orderOf_eq_one, one_pow]

/-- Odd-order lifts across an actual central 2-group kernel are unique. -/
theorem eq_of_odd_orderOf
    (hcentral : pi.ker ≤ Subgroup.center H) (hker : IsPGroup 2 pi.ker)
    {x y : H} (hmap : pi x = pi y)
    (hx : Odd (orderOf x)) (hy : Odd (orderOf y)) : x = y :=
  eq_of_coprime_orderOf pi hcentral hker hmap
    hx.coprime_two_left hy.coprime_two_left

end Kourovka2135.CentralPGroupOddLift
