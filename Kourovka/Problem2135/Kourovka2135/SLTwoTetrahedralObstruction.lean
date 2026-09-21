import Kourovka2135.SLTwoNonscalarWordValues
import Kourovka2135.OddPSLTwoProjectiveChart
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.LinearCombination

/-! Actual quaternion and order-three matrices give a uniform binary
product-order obstruction in SL₂ and PSL₂ over finite odd fields of size >3.
The required sum of two squares is supplied inside the actual prime field.
No subgroup recognition, Ore theorem, or bounded enumeration is an input.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.SLTwoTetrahedralObstruction

open scoped Matrix
open SLTwoNonscalarWordValues OddPSLTwoProjectiveChart

variable {F : Type*} [Field F]

def quaternionI : SLTwo.SL2 F := ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two_of]⟩

def quaternionJ (x y : F) (hxy : x ^ 2 + y ^ 2 = -1) : SLTwo.SL2 F :=
  ⟨!![x, y; y, -x], by
    simp only [Matrix.det_fin_two_of]
    linear_combination -hxy⟩

def quaternionK (x y : F) (hxy : x ^ 2 + y ^ 2 = -1) : SLTwo.SL2 F :=
  quaternionI * quaternionJ x y hxy

def tetrahedral (x y : F) (hxy : x ^ 2 + y ^ 2 = -1) (h2 : (2 : F) ≠ 0) :
    SLTwo.SL2 F :=
  ⟨!![(-1 + x + y) / 2, (1 + y - x) / 2;
      (-1 + y - x) / 2, (-1 - x - y) / 2], by
    simp only [Matrix.det_fin_two_of]
    field_simp
    linear_combination (-2 : F) * hxy⟩

theorem quaternionK_val (x y : F) (hxy : x ^ 2 + y ^ 2 = -1) :
    (quaternionK x y hxy).val = !![y, -x; -x, -y] := by
  change quaternionI.val * (quaternionJ x y hxy).val = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [quaternionI, quaternionJ, Matrix.mul_apply, Fin.sum_univ_two]

theorem quaternionK_sq (x y : F) (hxy : x ^ 2 + y ^ 2 = -1) :
    (quaternionK x y hxy).val ^ 2 = -(1 : Matrix (Fin 2) (Fin 2) F) := by
  rw [quaternionK_val, pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
    solve | ring | linear_combination hxy

theorem tetrahedral_inv_val (x y : F) (hxy : x ^ 2 + y ^ 2 = -1)
    (h2 : (2 : F) ≠ 0) :
    ((tetrahedral x y hxy h2)⁻¹).val = -1 - (tetrahedral x y hxy h2).val := by
  rw [Matrix.SpecialLinearGroup.coe_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tetrahedral, Matrix.adjugate_fin_two] <;> field_simp <;> ring

/-- The cube follows from the quadratic relation, avoiding a cubic entry expansion. -/
theorem tetrahedral_cube (x y : F) (hxy : x ^ 2 + y ^ 2 = -1)
    (h2 : (2 : F) ≠ 0) : tetrahedral x y hxy h2 ^ 3 = 1 := by
  let a := tetrahedral x y hxy h2
  have hi : a.val * (-1 - a.val) = 1 := by
    rw [← tetrahedral_inv_val x y hxy h2]
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hquad : a.val ^ 2 + a.val + 1 = 0 := by
    calc
      _ = -(a.val * (-1 - a.val) - 1) := by noncomm_ring
      _ = 0 := by rw [hi]; simp
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
  change a.val ^ 3 = 1
  calc
    _ = (a.val - 1) * (a.val ^ 2 + a.val + 1) + 1 := by noncomm_ring
    _ = 1 := by rw [hquad]; simp

theorem tetrahedral_nonscalar (x y : F) (hxy : x ^ 2 + y ^ 2 = -1)
    (h2 : (2 : F) ≠ 0) : Nonscalar (tetrahedral x y hxy h2) := by
  have hoff : (tetrahedral x y hxy h2).val 0 1 -
      (tetrahedral x y hxy h2).val 1 0 = 1 := by
    simp only [tetrahedral, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    field_simp
    ring
  rintro ⟨r, hr⟩
  simp [hr] at hoff

theorem nonscalar_of_trace_zero (g : SLTwo.SL2 F) (h2 : (2 : F) ≠ 0)
    (ht : g.val.trace = 0) : Nonscalar g := by
  rintro ⟨r, hr⟩
  have hh : (2 : F) * r = 0 := by
    simpa [hr, Matrix.trace_fin_two, two_mul] using ht
  have hr0 : r = 0 := (mul_eq_zero.mp hh).resolve_left h2
  have : (0 : F) = 1 := by simpa [hr, hr0] using g.prop
  exact zero_ne_one this

theorem quaternionK_nonscalar (x y : F) (hxy : x ^ 2 + y ^ 2 = -1)
    (h2 : (2 : F) ≠ 0) : Nonscalar (quaternionK x y hxy) :=
  nonscalar_of_trace_zero _ h2 (by simp [quaternionK_val, Matrix.trace_fin_two])

theorem tetrahedral_order (x y : F) (hxy : x ^ 2 + y ^ 2 = -1)
    (h2 : (2 : F) ≠ 0) : orderOf (tetrahedral x y hxy h2) = 3 := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  apply orderOf_eq_prime (tetrahedral_cube x y hxy h2)
  intro he
  apply tetrahedral_nonscalar x y hxy h2
  refine ⟨1, ?_⟩
  rw [he]
  simp

/-- The paper commutator convention gives [a,i]=ij, of order four. -/
theorem commutator_tetrahedral_i (x y : F) (hxy : x ^ 2 + y ^ 2 = -1)
    (h2 : (2 : F) ≠ 0) :
    paperCommutator (tetrahedral x y hxy h2) quaternionI = quaternionK x y hxy := by
  apply Subtype.ext
  simp only [paperCommutator, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv]
  rw [quaternionK_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tetrahedral, quaternionI, Matrix.adjugate_fin_two,
      Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp <;> solve | ring | linear_combination (2 : F) * hxy

theorem quaternionK_order (x y : F) (hxy : x ^ 2 + y ^ 2 = -1)
    (h2 : (2 : F) ≠ 0) : orderOf (quaternionK x y hxy) = 4 := by
  have hs := quaternionK_sq x y hxy
  have hn : quaternionK x y hxy ^ 2 ≠ 1 := by
    intro he
    have hmat := congrArg (fun g : SLTwo.SL2 F => g.val) he
    simp only [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one, hs] at hmat
    have hh : (-1 : F) = 1 := by
      simpa using congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 0 0) hmat
    apply h2
    linear_combination -hh
  have hp : quaternionK x y hxy ^ 4 = 1 := by
    apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
    rw [show 4 = 2 * 2 from rfl, pow_mul, hs]
    simp
  exact orderOf_eq_prime_pow (p := 2) (n := 1) hn hp

theorem not_productOrderCondition_sl2_of_parameters [Finite F]
    (hcard : 3 < Nat.card F) (x y : F) (hxy : x ^ 2 + y ^ 2 = -1)
    (h2 : (2 : F) ≠ 0) (w : OuterWord) : ¬ ProductOrderCondition w 2 (SLTwo.SL2 F) := by
  intro h
  have ha := nonscalar_mem_values hcard w _ (tetrahedral_nonscalar x y hxy h2)
  have hc : paperCommutator (tetrahedral x y hxy h2) quaternionI ∈
      w.values (SLTwo.SL2 F) := by
    rw [commutator_tetrahedral_i]
    exact nonscalar_mem_values hcard w _ (quaternionK_nonscalar x y hxy h2)
  have hn := h.not_dvd_orderOf_commutator ha
    (by rw [tetrahedral_order]; decide) hc
  apply hn
  change 2 ∣ orderOf (paperCommutator (tetrahedral x y hxy h2) quaternionI)
  rw [commutator_tetrahedral_i, quaternionK_order x y hxy h2]
  decide

theorem image_ne_one_of_nonscalar (g : SLTwo.SL2 F) (hg : Nonscalar g) :
    quotient F g ≠ 1 := by
  intro he
  have hc := (QuotientGroup.eq_one_iff g).mp he
  obtain ⟨r, _, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hc
  exact hg ⟨r, hr.symm⟩

theorem not_productOrderCondition_psl2_of_parameters [Finite F]
    (hcard : 3 < Nat.card F) (x y : F) (hxy : x ^ 2 + y ^ 2 = -1)
    (h2 : (2 : F) ≠ 0) (w : OuterWord) : ¬ ProductOrderCondition w 2 (Q F) := by
  let a := tetrahedral x y hxy h2
  let k := quaternionK x y hxy
  have haorder : orderOf (quotient F a) = 3 := by
    let : Fact (Nat.Prime 3) := ⟨by decide⟩
    apply orderOf_eq_prime
    · rw [← map_pow, tetrahedral_cube, map_one]
    · exact image_ne_one_of_nonscalar _ (tetrahedral_nonscalar x y hxy h2)
  have hkorder : orderOf (quotient F k) = 2 := by
    apply orderOf_eq_prime
    · rw [← map_pow]
      apply (QuotientGroup.eq_one_iff _).mpr
      apply Matrix.SpecialLinearGroup.mem_center_iff.mpr
      refine ⟨-1, by simp, ?_⟩
      rw [Matrix.SpecialLinearGroup.coe_pow, quaternionK_sq]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    · exact image_ne_one_of_nonscalar _ (quaternionK_nonscalar x y hxy h2)
  have hcomm : paperCommutator (quotient F a) (quotient F quaternionI) = quotient F k := by
    simpa only [paperCommutator, map_mul, map_inv] using
      congrArg (quotient F) (commutator_tetrahedral_i x y hxy h2)
  intro h
  have ha := w.map_mem_values (quotient F)
    (nonscalar_mem_values hcard w _ (tetrahedral_nonscalar x y hxy h2))
  have hc : paperCommutator (quotient F a) (quotient F quaternionI) ∈ w.values (Q F) := by
    rw [hcomm]
    exact w.map_mem_values (quotient F)
      (nonscalar_mem_values hcard w _ (quaternionK_nonscalar x y hxy h2))
  have hn := h.not_dvd_orderOf_commutator ha (by rw [haorder]; decide) hc
  apply hn
  change 2 ∣ orderOf (paperCommutator (quotient F a) (quotient F quaternionI))
  rw [hcomm, hkorder]

/-- The prime-field sum-of-squares theorem supplies actual quaternion matrices
uniformly, including characteristic three. -/
theorem not_productOrderCondition [Finite F] (hcard : 3 < Nat.card F)
    (hchar : ringChar F ≠ 2) (w : OuterWord) :
    ¬ ProductOrderCondition w 2 (SLTwo.SL2 F) ∧ ¬ ProductOrderCondition w 2 (Q F) := by
  let : NeZero (ringChar F) := ⟨CharP.ringChar_ne_zero_of_finite F⟩
  obtain ⟨m, n, hmn⟩ := CharP.sq_add_sq F (ringChar F) (-1)
  have hxy : (m : F) ^ 2 + (n : F) ^ 2 = -1 := by simpa only [Int.cast_neg, Int.cast_one] using hmn
  have h2 := Ring.two_ne_zero hchar
  exact ⟨not_productOrderCondition_sl2_of_parameters hcard m n hxy h2 w,
    not_productOrderCondition_psl2_of_parameters hcard m n hxy h2 w⟩

end Kourovka2135.SLTwoTetrahedralObstruction
