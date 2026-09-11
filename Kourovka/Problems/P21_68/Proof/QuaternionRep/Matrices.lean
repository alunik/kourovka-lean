import Mathlib.GroupTheory.SpecificGroups.Quaternion
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.RepresentationTheory.FinGroupCharZero
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Tactic

/-!
# The two-dimensional quaternion matrices

The matrices below realize the quaternion group of order eight over the complex
numbers. The extra matrix has order three and cycles the quaternion generators.
-/

noncomputable section

namespace Kourovka.P21_68

open Matrix

abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℂ

/-- The image of the quaternion generator `i`. -/
def matI : Mat2 := !![Complex.I, 0; 0, -Complex.I]

/-- The image of the quaternion generator `j`. -/
def matJ : Mat2 := !![0, 1; -1, 0]

/-- The image of the quaternion generator `k = ij`. -/
def matK : Mat2 := !![0, Complex.I; Complex.I, 0]

/-- A matrix of order three implementing the cycle `i → j → k → i`. -/
def matU : Mat2 := !![(-1 - Complex.I) / 2, (-1 - Complex.I) / 2;
  (1 - Complex.I) / 2, (-1 + Complex.I) / 2]

/-- Explicit powers of `matI`, indexed modulo four. -/
def matIPow (x : ZMod 4) : Mat2 := if x.val = 0 then 1 else if x.val = 1 then matI else if x.val = 2 then -1 else -matI

/-- The standard faithful quaternion representation, before bundling. -/
def quaternionMatrix : QuaternionGroup 2 → Mat2
  | .a x => matIPow x
  | .xa x => matJ * matIPow x

@[simp] theorem matI_mul_matJ : matI * matJ = matK := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matI, matJ, matK, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem matU_cube : matU ^ 3 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [matU, pow_succ, Matrix.mul_apply, Fin.sum_univ_two, Complex.ext_iff]

@[simp] theorem matU_mul_matI : matU * matI = matJ * matU := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [matU, matI, matJ, Matrix.mul_apply, Fin.sum_univ_two, Complex.ext_iff]

@[simp] theorem matU_mul_matJ : matU * matJ = matK * matU := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [matU, matK, matJ, Matrix.mul_apply, Fin.sum_univ_two, Complex.ext_iff]

@[simp] theorem quaternionMatrix_one : quaternionMatrix 1 = 1 := by
  rfl

/-- Integral matrices make the finite quaternion multiplication certificate small. -/
def quaternionIntegralMatrix : QuaternionGroup 2 → Matrix (Fin 2) (Fin 2) GaussianInt
  | .a x => ![1, !![⟨0, 1⟩, 0; 0, ⟨0, -1⟩], -1, !![⟨0, -1⟩, 0; 0, ⟨0, 1⟩]] x
  | .xa x => !![0, 1; -1, 0] *
      ![1, !![⟨0, 1⟩, 0; 0, ⟨0, -1⟩], -1, !![⟨0, -1⟩, 0; 0, ⟨0, 1⟩]] x

lemma quaternionIntegralMatrix_mul (q r : QuaternionGroup 2) :
    quaternionIntegralMatrix (q * r) = quaternionIntegralMatrix q * quaternionIntegralMatrix r := by
  revert q r
  decide +kernel

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 500000 in
lemma quaternionMatrix_eq_integral (q : QuaternionGroup 2) :
    quaternionMatrix q = (quaternionIntegralMatrix q).map GaussianInt.toComplex := by
  rcases q with q | q <;> fin_cases q <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [quaternionMatrix, matIPow, quaternionIntegralMatrix, matI, matJ,
      Matrix.map_apply, Matrix.mul_apply, Fin.sum_univ_two, GaussianInt.toComplex_def,
      GaussianInt.toComplex, Complex.ext_iff, ZMod.val]

/-- Quaternion multiplication follows from the exact integral certificate. -/
theorem quaternionMatrix_mul (q r : QuaternionGroup 2) :
    quaternionMatrix (q * r) = quaternionMatrix q * quaternionMatrix r := by
  rw [quaternionMatrix_eq_integral, quaternionIntegralMatrix_mul]
  rw [quaternionMatrix_eq_integral q, quaternionMatrix_eq_integral r]
  exact GaussianInt.toComplex.mapMatrix.map_mul _ _

/-- The matrix-valued quaternion representation. -/
def quaternionMatrixHom : QuaternionGroup 2 →* Mat2 where
  toFun := quaternionMatrix
  map_one' := quaternionMatrix_one
  map_mul' := quaternionMatrix_mul

end Kourovka.P21_68
