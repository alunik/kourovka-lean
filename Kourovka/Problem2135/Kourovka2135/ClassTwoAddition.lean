import Kourovka2135.ClassTwoCommutators
import Mathlib.Algebra.Group.MinimalAxioms

/-! The canonical additive operation in a class-two group with uniquely halved commutators. -/

set_option autoImplicit false
universe u
namespace Kourovka2135
variable {G : Type u} [Group G]

/-- The class-two addition formula, with `r` an inverse of two on the derived subgroup. -/
def classTwoSum (r : ℕ) (x y : G) : G := x * y * paperCommutator y x ^ r

variable (hD : commutator G ≤ Subgroup.center G)
include hD

private theorem commutator_central (x y : G) :
    paperCommutator x y ∈ Subgroup.center G := hD (paperCommutator_mem_commutator x y)

private theorem commutator_commutes (x y z : G) : Commute (paperCommutator x y) z :=
  (show Commute z (paperCommutator x y) from
    Subgroup.mem_center_iff.mp (commutator_central hD x y) z).symm

private theorem half_commutator_mul_left (r : ℕ) (x y z : G) :
    paperCommutator (x * y) z ^ r =
      paperCommutator x z ^ r * paperCommutator y z ^ r := by
  rw [paperCommutator_mul_left_of_central _ _ _ (commutator_central hD x z)]
  exact (commutator_commutes hD x z _).mul_pow r

private theorem half_commutator_mul_right (r : ℕ) (x y z : G) :
    paperCommutator x (y * z) ^ r =
      paperCommutator x y ^ r * paperCommutator x z ^ r := by
  rw [paperCommutator_mul_right_of_central _ _ _ (commutator_central hD x y)]
  exact (commutator_commutes hD x y _).mul_pow r

private theorem commutator_classTwoSum_right (r : ℕ) (x y z : G) :
    paperCommutator x (classTwoSum r y z) ^ r =
      paperCommutator x y ^ r * paperCommutator x z ^ r := by
  rw [classTwoSum, half_commutator_mul_right hD]
  have hz : paperCommutator x (paperCommutator z y ^ r) = 1 :=
    (paperCommutator_eq_one_iff _ _).mpr ((commutator_commutes hD z y x).pow_left r).symm
  rw [hz, one_pow, mul_one, half_commutator_mul_right hD]

private theorem commutator_classTwoSum_left (r : ℕ) (x y z : G) :
    paperCommutator (classTwoSum r x y) z ^ r =
      paperCommutator x z ^ r * paperCommutator y z ^ r := by
  rw [classTwoSum, half_commutator_mul_left hD]
  have hz : paperCommutator (paperCommutator y x ^ r) z = 1 :=
    (paperCommutator_eq_one_iff _ _).mpr ((commutator_commutes hD y x z).pow_left r)
  rw [hz, one_pow, mul_one, half_commutator_mul_left hD]

theorem classTwoSum_assoc (r : ℕ) (x y z : G) :
    classTwoSum r (classTwoSum r x y) z = classTwoSum r x (classTwoSum r y z) := by
  change (classTwoSum r x y * z) * paperCommutator z (classTwoSum r x y) ^ r =
    (x * classTwoSum r y z) * paperCommutator (classTwoSum r y z) x ^ r
  rw [commutator_classTwoSum_right hD, commutator_classTwoSum_left hD]
  unfold classTwoSum
  let a := paperCommutator y x ^ r
  let b := paperCommutator z x ^ r
  let c := paperCommutator z y ^ r
  change (x * y * a * z) * (b * c) = (x * (y * z * c)) * (a * b)
  have haz : Commute a z := (commutator_commutes hD y x z).pow_left r
  have hc : Commute c (a * b) := (commutator_commutes hD z y _).pow_left r
  calc
    (x * y * a * z) * (b * c) = (x * y * z) * (a * b * c) := by
      rw [mul_assoc (x * y) a z, haz.eq]
      simp only [mul_assoc]
    _ = (x * y * z) * (c * (a * b)) := by rw [hc.eq]
    _ = (x * (y * z * c)) * (a * b) := by simp only [mul_assoc]

omit hD in
theorem classTwoSum_comm (r : ℕ)
    (hhalf : ∀ c ∈ commutator G, c ^ (r + r) = c) (x y : G) :
    classTwoSum r x y = classTwoSum r y x := by
  have hh := hhalf (paperCommutator y x) (paperCommutator_mem_commutator y x)
  rw [pow_add] at hh
  have hswap : y * x = x * y * paperCommutator y x := by
    simp only [paperCommutator]
    group
  unfold classTwoSum
  rw [hswap, ← paperCommutator_inv_swap y x, inv_pow, mul_assoc (x * y)]
  apply congrArg (fun z => x * y * z)
  exact (eq_mul_inv_iff_mul_eq).mpr hh

omit hD in
@[simp] theorem classTwoSum_one_left (r : ℕ) (x : G) : classTwoSum r 1 x = x := by
  simp [classTwoSum, paperCommutator]

omit hD in
@[simp] theorem classTwoSum_inv_left (r : ℕ) (x : G) : classTwoSum r x⁻¹ x = 1 := by
  simp [classTwoSum, paperCommutator]

omit hD in
theorem classTwoSum_of_commute (r : ℕ) (x y : G) (h : Commute x y) :
    classTwoSum r x y = x * y := by
  rw [classTwoSum, (paperCommutator_eq_one_iff _ _).mpr h.symm, one_pow, mul_one]

end Kourovka2135
