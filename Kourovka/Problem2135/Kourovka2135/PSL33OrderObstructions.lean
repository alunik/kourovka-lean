import Kourovka2135.PSL33GoodSets

/-! Explicit violations of the product-order condition in PSL(3,3), for
every outer word and each prime dividing the group order. -/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace Kourovka2135.PSL33OrderObstructions
open SL33Witnesses PSL33GoodSets
open scoped MatrixGroups

def g2 : S := ⟨!![0, 2, 0; 0, 0, 2; 1, 1, 0], by decide⟩
def v2 : S := ⟨!![0, 1, 1; 1, 2, 1; 0, 1, 0], by decide⟩
def g3 : S := ⟨!![0, 2, 0; 0, 0, 2; 1, 2, 0], by decide⟩
def v3 : S := ⟨!![1, 1, 2; 2, 1, 1; 1, 2, 1], by decide⟩

theorem v2_conjugate : g2⁻¹ * a13 * g2 = v2 := by decide
theorem v3_commutator : paperCommutator a8 (g3⁻¹ * a13 * g3) = v3 := by decide
theorem v3_cube : v3 ^ 3 = 1 := by decide
theorem product2_cube : (a8 * v2) ^ 3 = 1 := by decide

def z : S := ⟨!![2, 2, 0; 1, 2, 1; 1, 2, 0], by decide⟩
def z2 : S := ⟨!![0, 2, 2; 2, 2, 2; 1, 0, 2], by decide⟩
def z4 : S := ⟨!![0, 1, 2; 0, 2, 0; 2, 2, 0], by decide⟩
theorem product3 : a8 * v3 = z := by decide
theorem z_square : z * z = z2 := by decide
theorem z2_square : z2 * z2 = z4 := by decide
theorem z4_square : z4 * z4 = 1 := by decide
theorem product3_eighth : (a8 * v3) ^ 8 = 1 := by
  have h2 : z ^ 2 = z2 := by simpa only [pow_two] using z_square
  have h4 : z ^ 4 = z4 := by
    calc
      z ^ 4 = z ^ 2 * z ^ 2 := pow_add z 2 2
      _ = z4 := by rw [h2, z2_square]
  rw [product3]
  calc
    z ^ 8 = z ^ 4 * z ^ 4 := pow_add z 4 4
    _ = 1 := by rw [h4, z4_square]

theorem order_y8 : orderOf y8 = 8 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply orderOf_eq_prime_pow (p := 2) (n := 2)
  · intro he
    have hc : a8 ^ 4 ∈ Subgroup.center S := by
      apply (QuotientGroup.eq_one_iff _).mp
      change q (a8 ^ 4) = 1
      change q a8 ^ 4 = 1 at he
      simpa only [map_pow] using he
    have hc' := Subgroup.mem_center_iff.mp hc b8
    exact (by decide : b8 * a8 ^ 4 ≠ a8 ^ 4 * b8) hc'
  · change q a8 ^ 8 = 1
    rw [← map_pow, power8, map_one]

theorem v2_mem_values (w : OuterWord) : q v2 ∈ w.values Q := by
  rw [← v2_conjugate, map_mul, map_mul, map_inv]
  exact w.conj_mem_values (good13.subset_values w y13_mem) (q g2)

theorem order_v2 : orderOf (q v2) = 13 := by
  rw [← v2_conjugate, map_mul, map_mul, map_inv]
  have he := (MulAut.conj (q g2)⁻¹).orderOf_eq y13
  simpa only [MulAut.conj_apply, inv_inv, y13] using he.trans order_y13

theorem v3_mem_values (w : OuterWord) : q v3 ∈ w.values Q := by
  cases w with
  | leaf => simp
  | bracket l r =>
    apply (OuterWord.mem_values_bracket l r _).mpr
    refine ⟨y8, good8.subset_values l y8_mem,
      (q g3)⁻¹ * y13 * q g3, r.conj_mem_values (good13.subset_values r y13_mem) (q g3), ?_⟩
    have he := congrArg q v3_commutator
    simpa only [paperCommutator, map_mul, map_inv, y8, y13] using he

theorem v3_ne_one : q v3 ≠ 1 := by
  intro he
  have hc : v3 ∈ Subgroup.center S := (QuotientGroup.eq_one_iff _).mp he
  exact (by decide : a8 * v3 ≠ v3 * a8) (Subgroup.mem_center_iff.mp hc a8)

theorem order_v3 : orderOf (q v3) = 3 := by
  apply orderOf_eq_prime ?_ v3_ne_one
  rw [← map_pow, v3_cube, map_one]

theorem product2_not_dvd : ¬ 13 ∣ orderOf (y8 * q v2) := by
  have he : (y8 * q v2) ^ 3 = 1 := by
    change (q a8 * q v2) ^ 3 = 1
    rw [← map_mul, ← map_pow, product2_cube, map_one]
  intro hd
  exact (by decide : ¬ 13 ∣ 3) (hd.trans (orderOf_dvd_of_pow_eq_one he))

theorem product2_swap_not_dvd : ¬ 2 ∣ orderOf (q v2 * y8) := by
  have he : (q v2 * y8) ^ 3 = 1 := by
    have hh : (v2 * a8) ^ 3 = 1 := by decide
    change (q v2 * q a8) ^ 3 = 1
    rw [← map_mul, ← map_pow, hh, map_one]
  intro hd
  exact (by decide : ¬ 2 ∣ 3) (hd.trans (orderOf_dvd_of_pow_eq_one he))

theorem not_condition_two (w : OuterWord) : ¬ ProductOrderCondition w 2 Q := by
  intro h
  exact product2_swap_not_dvd
    (h (q v2) (v2_mem_values w) y8 (good8.subset_values w y8_mem)
      (by rw [order_v2]; decide) (by rw [order_y8]; decide))

theorem not_condition_thirteen (w : OuterWord) : ¬ ProductOrderCondition w 13 Q := by
  intro h
  exact product2_not_dvd
    (h y8 (good8.subset_values w y8_mem) (q v2) (v2_mem_values w)
      (by rw [order_y8]; decide) (by rw [order_v2]))

theorem not_condition_three (w : OuterWord) : ¬ ProductOrderCondition w 3 Q := by
  intro h
  have hd := h y8 (good8.subset_values w y8_mem) (q v3) (v3_mem_values w)
    (by rw [order_y8]; decide) (by rw [order_v3])
  have he : (y8 * q v3) ^ 8 = 1 := by
    change (q a8 * q v3) ^ 8 = 1
    rw [← map_mul, ← map_pow, product3_eighth, map_one]
  exact (by decide : ¬ 3 ∣ 8) (hd.trans (orderOf_dvd_of_pow_eq_one he))

end Kourovka2135.PSL33OrderObstructions
