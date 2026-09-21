import Kourovka2135.SuzukiEightCodeField
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Tactic

/-! Exact canonical component, with polynomial-bit codes and ordinary kernel checks. -/
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
namespace Kourovka2135.SuzukiEightCoverCodeMatrices
open SuzukiEightCodeField
abbrev M := Matrix (Fin 4) (Fin 4) Element
abbrev UnitMatrix := Matrix.GeneralLinearGroup (Fin 4) Element

def cMatrix : M := !![ofCode 0, ofCode 0, ofCode 0, ofCode 1; ofCode 0, ofCode 0, ofCode 1, ofCode 0; ofCode 0, ofCode 1, ofCode 0, ofCode 0; ofCode 1, ofCode 0, ofCode 0, ofCode 0]
def cInverse : M := !![ofCode 0, ofCode 0, ofCode 0, ofCode 1; ofCode 0, ofCode 0, ofCode 1, ofCode 0; ofCode 0, ofCode 1, ofCode 0, ofCode 0; ofCode 1, ofCode 0, ofCode 0, ofCode 0]
theorem c_mul_inverse : cMatrix * cInverse = 1 := by decide +kernel
theorem c_inverse_mul : cInverse * cMatrix = 1 := by decide +kernel
def c : UnitMatrix := ⟨cMatrix, cInverse, c_mul_inverse, c_inverse_mul⟩

def bMatrix : M := !![ofCode 1, ofCode 3, ofCode 0, ofCode 6; ofCode 0, ofCode 1, ofCode 7, ofCode 2; ofCode 0, ofCode 0, ofCode 1, ofCode 3; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
def bInverse : M := !![ofCode 1, ofCode 3, ofCode 2, ofCode 6; ofCode 0, ofCode 1, ofCode 7, ofCode 0; ofCode 0, ofCode 0, ofCode 1, ofCode 3; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
theorem b_mul_inverse : bMatrix * bInverse = 1 := by decide +kernel
theorem b_inverse_mul : bInverse * bMatrix = 1 := by decide +kernel
def b : UnitMatrix := ⟨bMatrix, bInverse, b_mul_inverse, b_inverse_mul⟩

def torusMatrix : M := !![ofCode 4, ofCode 0, ofCode 0, ofCode 0; ofCode 0, ofCode 5, ofCode 0, ofCode 0; ofCode 0, ofCode 0, ofCode 2, ofCode 0; ofCode 0, ofCode 0, ofCode 0, ofCode 7]
def torusInverse : M := !![ofCode 7, ofCode 0, ofCode 0, ofCode 0; ofCode 0, ofCode 2, ofCode 0, ofCode 0; ofCode 0, ofCode 0, ofCode 5, ofCode 0; ofCode 0, ofCode 0, ofCode 0, ofCode 4]
theorem torus_mul_inverse : torusMatrix * torusInverse = 1 := by decide +kernel
theorem torus_inverse_mul : torusInverse * torusMatrix = 1 := by decide +kernel
def torus : UnitMatrix := ⟨torusMatrix, torusInverse, torus_mul_inverse, torus_inverse_mul⟩

def pc0Matrix : M := !![ofCode 1, ofCode 4, ofCode 0, ofCode 7; ofCode 0, ofCode 1, ofCode 2, ofCode 3; ofCode 0, ofCode 0, ofCode 1, ofCode 4; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
def pc0Inverse : M := !![ofCode 1, ofCode 4, ofCode 3, ofCode 7; ofCode 0, ofCode 1, ofCode 2, ofCode 0; ofCode 0, ofCode 0, ofCode 1, ofCode 4; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
theorem pc0_mul_inverse : pc0Matrix * pc0Inverse = 1 := by decide +kernel
theorem pc0_inverse_mul : pc0Inverse * pc0Matrix = 1 := by decide +kernel
def pc0 : UnitMatrix := ⟨pc0Matrix, pc0Inverse, pc0_mul_inverse, pc0_inverse_mul⟩

def pc1Matrix : M := !![ofCode 1, ofCode 2, ofCode 0, ofCode 5; ofCode 0, ofCode 1, ofCode 6, ofCode 7; ofCode 0, ofCode 0, ofCode 1, ofCode 2; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
def pc1Inverse : M := !![ofCode 1, ofCode 2, ofCode 7, ofCode 5; ofCode 0, ofCode 1, ofCode 6, ofCode 0; ofCode 0, ofCode 0, ofCode 1, ofCode 2; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
theorem pc1_mul_inverse : pc1Matrix * pc1Inverse = 1 := by decide +kernel
theorem pc1_inverse_mul : pc1Inverse * pc1Matrix = 1 := by decide +kernel
def pc1 : UnitMatrix := ⟨pc1Matrix, pc1Inverse, pc1_mul_inverse, pc1_inverse_mul⟩

def pc2Matrix : M := !![ofCode 1, ofCode 1, ofCode 0, ofCode 1; ofCode 0, ofCode 1, ofCode 1, ofCode 1; ofCode 0, ofCode 0, ofCode 1, ofCode 1; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
def pc2Inverse : M := !![ofCode 1, ofCode 1, ofCode 1, ofCode 1; ofCode 0, ofCode 1, ofCode 1, ofCode 0; ofCode 0, ofCode 0, ofCode 1, ofCode 1; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
theorem pc2_mul_inverse : pc2Matrix * pc2Inverse = 1 := by decide +kernel
theorem pc2_inverse_mul : pc2Inverse * pc2Matrix = 1 := by decide +kernel
def pc2 : UnitMatrix := ⟨pc2Matrix, pc2Inverse, pc2_mul_inverse, pc2_inverse_mul⟩

def pc3Matrix : M := !![ofCode 1, ofCode 0, ofCode 4, ofCode 2; ofCode 0, ofCode 1, ofCode 0, ofCode 4; ofCode 0, ofCode 0, ofCode 1, ofCode 0; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
def pc3Inverse : M := !![ofCode 1, ofCode 0, ofCode 4, ofCode 2; ofCode 0, ofCode 1, ofCode 0, ofCode 4; ofCode 0, ofCode 0, ofCode 1, ofCode 0; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
theorem pc3_mul_inverse : pc3Matrix * pc3Inverse = 1 := by decide +kernel
theorem pc3_inverse_mul : pc3Inverse * pc3Matrix = 1 := by decide +kernel
def pc3 : UnitMatrix := ⟨pc3Matrix, pc3Inverse, pc3_mul_inverse, pc3_inverse_mul⟩

def pc4Matrix : M := !![ofCode 1, ofCode 0, ofCode 2, ofCode 6; ofCode 0, ofCode 1, ofCode 0, ofCode 2; ofCode 0, ofCode 0, ofCode 1, ofCode 0; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
def pc4Inverse : M := !![ofCode 1, ofCode 0, ofCode 2, ofCode 6; ofCode 0, ofCode 1, ofCode 0, ofCode 2; ofCode 0, ofCode 0, ofCode 1, ofCode 0; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
theorem pc4_mul_inverse : pc4Matrix * pc4Inverse = 1 := by decide +kernel
theorem pc4_inverse_mul : pc4Inverse * pc4Matrix = 1 := by decide +kernel
def pc4 : UnitMatrix := ⟨pc4Matrix, pc4Inverse, pc4_mul_inverse, pc4_inverse_mul⟩

def pc5Matrix : M := !![ofCode 1, ofCode 0, ofCode 1, ofCode 1; ofCode 0, ofCode 1, ofCode 0, ofCode 1; ofCode 0, ofCode 0, ofCode 1, ofCode 0; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
def pc5Inverse : M := !![ofCode 1, ofCode 0, ofCode 1, ofCode 1; ofCode 0, ofCode 1, ofCode 0, ofCode 1; ofCode 0, ofCode 0, ofCode 1, ofCode 0; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
theorem pc5_mul_inverse : pc5Matrix * pc5Inverse = 1 := by decide +kernel
theorem pc5_inverse_mul : pc5Inverse * pc5Matrix = 1 := by decide +kernel
def pc5 : UnitMatrix := ⟨pc5Matrix, pc5Inverse, pc5_mul_inverse, pc5_inverse_mul⟩

def pc6Matrix : M := !![ofCode 1, ofCode 0, ofCode 0, ofCode 0; ofCode 0, ofCode 1, ofCode 0, ofCode 0; ofCode 0, ofCode 0, ofCode 1, ofCode 0; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
def pc6Inverse : M := !![ofCode 1, ofCode 0, ofCode 0, ofCode 0; ofCode 0, ofCode 1, ofCode 0, ofCode 0; ofCode 0, ofCode 0, ofCode 1, ofCode 0; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
theorem pc6_mul_inverse : pc6Matrix * pc6Inverse = 1 := by decide +kernel
theorem pc6_inverse_mul : pc6Inverse * pc6Matrix = 1 := by decide +kernel
def pc6 : UnitMatrix := ⟨pc6Matrix, pc6Inverse, pc6_mul_inverse, pc6_inverse_mul⟩

def pc7Matrix : M := !![ofCode 1, ofCode 0, ofCode 0, ofCode 0; ofCode 0, ofCode 1, ofCode 0, ofCode 0; ofCode 0, ofCode 0, ofCode 1, ofCode 0; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
def pc7Inverse : M := !![ofCode 1, ofCode 0, ofCode 0, ofCode 0; ofCode 0, ofCode 1, ofCode 0, ofCode 0; ofCode 0, ofCode 0, ofCode 1, ofCode 0; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
theorem pc7_mul_inverse : pc7Matrix * pc7Inverse = 1 := by decide +kernel
theorem pc7_inverse_mul : pc7Inverse * pc7Matrix = 1 := by decide +kernel
def pc7 : UnitMatrix := ⟨pc7Matrix, pc7Inverse, pc7_mul_inverse, pc7_inverse_mul⟩

private def pc0Prefix1 : M := !![ofCode 6, ofCode 0, ofCode 3, ofCode 1; ofCode 2, ofCode 7, ofCode 1, ofCode 0; ofCode 3, ofCode 1, ofCode 0, ofCode 0; ofCode 1, ofCode 0, ofCode 0, ofCode 0]
private theorem pc0Step1 : bMatrix * cMatrix = pc0Prefix1 := by decide +kernel
private def pc0Prefix2 : M := !![ofCode 6, ofCode 1, ofCode 3, ofCode 6; ofCode 2, ofCode 1, ofCode 2, ofCode 1; ofCode 3, ofCode 4, ofCode 7, ofCode 3; ofCode 1, ofCode 3, ofCode 0, ofCode 6]
private theorem pc0Step2 : pc0Prefix1 * bMatrix = pc0Prefix2 := by decide +kernel
private def pc0Prefix3 : M := !![ofCode 6, ofCode 3, ofCode 1, ofCode 6; ofCode 1, ofCode 2, ofCode 1, ofCode 2; ofCode 3, ofCode 7, ofCode 4, ofCode 3; ofCode 6, ofCode 0, ofCode 3, ofCode 1]
private theorem pc0Step3 : pc0Prefix2 * cMatrix = pc0Prefix3 := by decide +kernel
private def pc0Prefix4 : M := !![ofCode 6, ofCode 2, ofCode 3, ofCode 1; ofCode 1, ofCode 1, ofCode 4, ofCode 3; ofCode 3, ofCode 2, ofCode 7, ofCode 0; ofCode 6, ofCode 1, ofCode 3, ofCode 6]
private theorem pc0Step4 : pc0Prefix3 * bMatrix = pc0Prefix4 := by decide +kernel
private def pc0Prefix5 : M := !![ofCode 6, ofCode 3, ofCode 6, ofCode 2; ofCode 1, ofCode 2, ofCode 3, ofCode 0; ofCode 3, ofCode 7, ofCode 2, ofCode 7; ofCode 6, ofCode 0, ofCode 4, ofCode 3]
private theorem pc0Step5 : pc0Prefix4 * bMatrix = pc0Prefix5 := by decide +kernel
private def pc0Prefix6 : M := !![ofCode 2, ofCode 6, ofCode 3, ofCode 6; ofCode 0, ofCode 3, ofCode 2, ofCode 1; ofCode 7, ofCode 2, ofCode 7, ofCode 3; ofCode 3, ofCode 4, ofCode 0, ofCode 6]
private theorem pc0Step6 : pc0Prefix5 * cMatrix = pc0Prefix6 := by decide +kernel
private def pc0Prefix7 : M := !![ofCode 2, ofCode 0, ofCode 7, ofCode 3; ofCode 0, ofCode 3, ofCode 0, ofCode 1; ofCode 7, ofCode 0, ofCode 2, ofCode 1; ofCode 3, ofCode 1, ofCode 1, ofCode 4]
private theorem pc0Step7 : pc0Prefix6 * bMatrix = pc0Prefix7 := by decide +kernel
private def pc0Prefix8 : M := !![ofCode 2, ofCode 6, ofCode 7, ofCode 6; ofCode 0, ofCode 3, ofCode 2, ofCode 7; ofCode 7, ofCode 2, ofCode 2, ofCode 3; ofCode 3, ofCode 4, ofCode 6, ofCode 4]
private theorem pc0Step8 : pc0Prefix7 * bMatrix = pc0Prefix8 := by decide +kernel
private def pc0Prefix9 : M := !![ofCode 6, ofCode 7, ofCode 6, ofCode 2; ofCode 7, ofCode 2, ofCode 3, ofCode 0; ofCode 3, ofCode 2, ofCode 2, ofCode 7; ofCode 4, ofCode 6, ofCode 4, ofCode 3]
private theorem pc0Step9 : pc0Prefix8 * cMatrix = pc0Prefix9 := by decide +kernel
private def pc0Prefix10 : M := !![ofCode 6, ofCode 6, ofCode 2, ofCode 1; ofCode 7, ofCode 0, ofCode 3, ofCode 1; ofCode 3, ofCode 7, ofCode 1, ofCode 0; ofCode 4, ofCode 1, ofCode 3, ofCode 1]
private theorem pc0Step10 : pc0Prefix9 * bInverse = pc0Prefix10 := by decide +kernel
private def pc0Prefix11 : M := !![ofCode 1, ofCode 2, ofCode 6, ofCode 6; ofCode 1, ofCode 3, ofCode 0, ofCode 7; ofCode 0, ofCode 1, ofCode 7, ofCode 3; ofCode 1, ofCode 3, ofCode 1, ofCode 4]
private theorem pc0Step11 : pc0Prefix10 * cMatrix = pc0Prefix11 := by decide +kernel
private def pc0Prefix12 : M := !![ofCode 1, ofCode 1, ofCode 3, ofCode 5; ofCode 1, ofCode 0, ofCode 2, ofCode 7; ofCode 0, ofCode 1, ofCode 0, ofCode 3; ofCode 1, ofCode 0, ofCode 3, ofCode 7]
private theorem pc0Step12 : pc0Prefix11 * bMatrix = pc0Prefix12 := by decide +kernel
private def pc0Prefix13 : M := !![ofCode 1, ofCode 2, ofCode 4, ofCode 4; ofCode 1, ofCode 3, ofCode 2, ofCode 7; ofCode 0, ofCode 1, ofCode 7, ofCode 1; ofCode 1, ofCode 3, ofCode 3, ofCode 4]
private theorem pc0Step13 : pc0Prefix12 * bMatrix = pc0Prefix13 := by decide +kernel
private def pc0Prefix14 : M := !![ofCode 4, ofCode 4, ofCode 2, ofCode 1; ofCode 7, ofCode 2, ofCode 3, ofCode 1; ofCode 1, ofCode 7, ofCode 1, ofCode 0; ofCode 4, ofCode 3, ofCode 3, ofCode 1]
private theorem pc0Step14 : pc0Prefix13 * cMatrix = pc0Prefix14 := by decide +kernel
private def pc0Prefix15 : M := !![ofCode 4, ofCode 3, ofCode 3, ofCode 1; ofCode 7, ofCode 0, ofCode 6, ofCode 4; ofCode 1, ofCode 4, ofCode 2, ofCode 0; ofCode 4, ofCode 4, ofCode 1, ofCode 7]
private theorem pc0Step15 : pc0Prefix14 * bMatrix = pc0Prefix15 := by decide +kernel
private def pc0Prefix16 : M := !![ofCode 4, ofCode 4, ofCode 1, ofCode 7; ofCode 7, ofCode 2, ofCode 6, ofCode 1; ofCode 1, ofCode 7, ofCode 3, ofCode 3; ofCode 4, ofCode 3, ofCode 0, ofCode 2]
private theorem pc0Step16 : pc0Prefix15 * bMatrix = pc0Prefix16 := by decide +kernel
private def pc0Prefix17 : M := !![ofCode 7, ofCode 1, ofCode 4, ofCode 4; ofCode 1, ofCode 6, ofCode 2, ofCode 7; ofCode 3, ofCode 3, ofCode 7, ofCode 1; ofCode 2, ofCode 0, ofCode 3, ofCode 4]
private theorem pc0Step17 : pc0Prefix16 * cMatrix = pc0Prefix17 := by decide +kernel
private def pc0Prefix18 : M := !![ofCode 7, ofCode 3, ofCode 3, ofCode 5; ofCode 1, ofCode 5, ofCode 6, ofCode 0; ofCode 3, ofCode 6, ofCode 5, ofCode 4; ofCode 2, ofCode 6, ofCode 3, ofCode 6]
private theorem pc0Step18 : pc0Prefix17 * bMatrix = pc0Prefix18 := by decide +kernel
private def pc0Prefix19 : M := !![ofCode 5, ofCode 3, ofCode 3, ofCode 7; ofCode 0, ofCode 6, ofCode 5, ofCode 1; ofCode 4, ofCode 5, ofCode 6, ofCode 3; ofCode 6, ofCode 3, ofCode 6, ofCode 2]
private theorem pc0Step19 : pc0Prefix18 * cMatrix = pc0Prefix19 := by decide +kernel
private def pc0Prefix20 : M := !![ofCode 5, ofCode 7, ofCode 0, ofCode 1; ofCode 0, ofCode 6, ofCode 1, ofCode 5; ofCode 4, ofCode 2, ofCode 3, ofCode 7; ofCode 6, ofCode 2, ofCode 3, ofCode 1]
private theorem pc0Step20 : pc0Prefix19 * bInverse = pc0Prefix20 := by decide +kernel
private def pc0Prefix21 : M := !![ofCode 1, ofCode 0, ofCode 7, ofCode 5; ofCode 5, ofCode 1, ofCode 6, ofCode 0; ofCode 7, ofCode 3, ofCode 2, ofCode 4; ofCode 1, ofCode 3, ofCode 2, ofCode 6]
private theorem pc0Step21 : pc0Prefix20 * cMatrix = pc0Prefix21 := by decide +kernel
private def pc0Prefix22 : M := !![ofCode 1, ofCode 3, ofCode 7, ofCode 1; ofCode 5, ofCode 5, ofCode 1, ofCode 0; ofCode 7, ofCode 1, ofCode 0, ofCode 0; ofCode 1, ofCode 0, ofCode 0, ofCode 0]
private theorem pc0Step22 : pc0Prefix21 * bMatrix = pc0Prefix22 := by decide +kernel
private def pc0Prefix23 : M := !![ofCode 1, ofCode 7, ofCode 3, ofCode 1; ofCode 0, ofCode 1, ofCode 5, ofCode 5; ofCode 0, ofCode 0, ofCode 1, ofCode 7; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem pc0Step23 : pc0Prefix22 * cMatrix = pc0Prefix23 := by decide +kernel
private theorem pc0Step24 : pc0Prefix23 * bMatrix = pc0Matrix := by decide +kernel

theorem pc0_from_cb : b * c * b * c * b * b * c * b * b * c * b⁻¹ * c * b * b * c * b * b * c * b * c * b⁻¹ * c * b * c * b = pc0 := by
  apply Units.ext
  change bMatrix * cMatrix * bMatrix * cMatrix * bMatrix * bMatrix * cMatrix * bMatrix * bMatrix * cMatrix * bInverse * cMatrix * bMatrix * bMatrix * cMatrix * bMatrix * bMatrix * cMatrix * bMatrix * cMatrix * bInverse * cMatrix * bMatrix * cMatrix * bMatrix = pc0Matrix
  rw [pc0Step1, pc0Step2, pc0Step3, pc0Step4, pc0Step5, pc0Step6, pc0Step7, pc0Step8, pc0Step9, pc0Step10, pc0Step11, pc0Step12, pc0Step13, pc0Step14, pc0Step15, pc0Step16, pc0Step17, pc0Step18, pc0Step19, pc0Step20, pc0Step21, pc0Step22, pc0Step23, pc0Step24]

private def pc1Prefix1 : M := !![ofCode 6, ofCode 0, ofCode 3, ofCode 1; ofCode 2, ofCode 7, ofCode 1, ofCode 0; ofCode 3, ofCode 1, ofCode 0, ofCode 0; ofCode 1, ofCode 0, ofCode 0, ofCode 0]
private theorem pc1Step1 : bMatrix * cMatrix = pc1Prefix1 := by decide +kernel
private def pc1Prefix2 : M := !![ofCode 6, ofCode 1, ofCode 3, ofCode 6; ofCode 2, ofCode 1, ofCode 2, ofCode 1; ofCode 3, ofCode 4, ofCode 7, ofCode 3; ofCode 1, ofCode 3, ofCode 0, ofCode 6]
private theorem pc1Step2 : pc1Prefix1 * bMatrix = pc1Prefix2 := by decide +kernel
private def pc1Prefix3 : M := !![ofCode 6, ofCode 0, ofCode 4, ofCode 3; ofCode 2, ofCode 7, ofCode 5, ofCode 2; ofCode 3, ofCode 1, ofCode 6, ofCode 3; ofCode 1, ofCode 0, ofCode 2, ofCode 6]
private theorem pc1Step3 : pc1Prefix2 * bMatrix = pc1Prefix3 := by decide +kernel
private def pc1Prefix4 : M := !![ofCode 3, ofCode 4, ofCode 0, ofCode 6; ofCode 2, ofCode 5, ofCode 7, ofCode 2; ofCode 3, ofCode 6, ofCode 1, ofCode 3; ofCode 6, ofCode 2, ofCode 0, ofCode 1]
private theorem pc1Step4 : pc1Prefix3 * cMatrix = pc1Prefix4 := by decide +kernel
private def pc1Prefix5 : M := !![ofCode 3, ofCode 1, ofCode 7, ofCode 7; ofCode 2, ofCode 3, ofCode 5, ofCode 7; ofCode 3, ofCode 3, ofCode 3, ofCode 1; ofCode 6, ofCode 3, ofCode 2, ofCode 3]
private theorem pc1Step5 : pc1Prefix4 * bInverse = pc1Prefix5 := by decide +kernel
private def pc1Prefix6 : M := !![ofCode 7, ofCode 7, ofCode 1, ofCode 3; ofCode 7, ofCode 5, ofCode 3, ofCode 2; ofCode 1, ofCode 3, ofCode 3, ofCode 3; ofCode 3, ofCode 2, ofCode 3, ofCode 6]
private theorem pc1Step6 : pc1Prefix5 * cMatrix = pc1Prefix6 := by decide +kernel
private def pc1Prefix7 : M := !![ofCode 7, ofCode 5, ofCode 2, ofCode 1; ofCode 7, ofCode 7, ofCode 5, ofCode 2; ofCode 1, ofCode 0, ofCode 1, ofCode 6; ofCode 3, ofCode 7, ofCode 6, ofCode 6]
private theorem pc1Step7 : pc1Prefix6 * bMatrix = pc1Prefix7 := by decide +kernel
private def pc1Prefix8 : M := !![ofCode 7, ofCode 7, ofCode 4, ofCode 2; ofCode 7, ofCode 5, ofCode 6, ofCode 7; ofCode 1, ofCode 3, ofCode 1, ofCode 3; ofCode 3, ofCode 2, ofCode 5, ofCode 3]
private theorem pc1Step8 : pc1Prefix7 * bMatrix = pc1Prefix8 := by decide +kernel
private def pc1Prefix9 : M := !![ofCode 2, ofCode 4, ofCode 7, ofCode 7; ofCode 7, ofCode 6, ofCode 5, ofCode 7; ofCode 3, ofCode 1, ofCode 3, ofCode 1; ofCode 3, ofCode 5, ofCode 2, ofCode 3]
private theorem pc1Step9 : pc1Prefix8 * cMatrix = pc1Prefix9 := by decide +kernel
private def pc1Prefix10 : M := !![ofCode 2, ofCode 2, ofCode 6, ofCode 1; ofCode 7, ofCode 4, ofCode 1, ofCode 0; ofCode 3, ofCode 4, ofCode 4, ofCode 7; ofCode 3, ofCode 0, ofCode 4, ofCode 5]
private theorem pc1Step10 : pc1Prefix9 * bMatrix = pc1Prefix10 := by decide +kernel
private def pc1Prefix11 : M := !![ofCode 1, ofCode 6, ofCode 2, ofCode 2; ofCode 0, ofCode 1, ofCode 4, ofCode 7; ofCode 7, ofCode 4, ofCode 4, ofCode 3; ofCode 5, ofCode 4, ofCode 0, ofCode 3]
private theorem pc1Step11 : pc1Prefix10 * cMatrix = pc1Prefix11 := by decide +kernel
private def pc1Prefix12 : M := !![ofCode 1, ofCode 5, ofCode 4, ofCode 2; ofCode 0, ofCode 1, ofCode 3, ofCode 0; ofCode 7, ofCode 6, ofCode 0, ofCode 0; ofCode 5, ofCode 0, ofCode 0, ofCode 0]
private theorem pc1Step12 : pc1Prefix11 * bInverse = pc1Prefix12 := by decide +kernel
private def pc1Prefix13 : M := !![ofCode 2, ofCode 4, ofCode 5, ofCode 1; ofCode 0, ofCode 3, ofCode 1, ofCode 0; ofCode 0, ofCode 0, ofCode 6, ofCode 7; ofCode 0, ofCode 0, ofCode 0, ofCode 5]
private theorem pc1Step13 : pc1Prefix12 * cMatrix = pc1Prefix13 := by decide +kernel
private def pc1Prefix14 : M := !![ofCode 2, ofCode 2, ofCode 0, ofCode 2; ofCode 0, ofCode 3, ofCode 3, ofCode 3; ofCode 0, ofCode 0, ofCode 6, ofCode 6; ofCode 0, ofCode 0, ofCode 0, ofCode 5]
private theorem pc1Step14 : pc1Prefix13 * bInverse = pc1Prefix14 := by decide +kernel
private def pc1Prefix15 : M := !![ofCode 2, ofCode 0, ofCode 2, ofCode 2; ofCode 3, ofCode 3, ofCode 3, ofCode 0; ofCode 6, ofCode 6, ofCode 0, ofCode 0; ofCode 5, ofCode 0, ofCode 0, ofCode 0]
private theorem pc1Step15 : pc1Prefix14 * cMatrix = pc1Prefix15 := by decide +kernel
private def pc1Prefix16 : M := !![ofCode 2, ofCode 6, ofCode 2, ofCode 3; ofCode 3, ofCode 6, ofCode 1, ofCode 2; ofCode 6, ofCode 7, ofCode 4, ofCode 5; ofCode 5, ofCode 4, ofCode 0, ofCode 3]
private theorem pc1Step16 : pc1Prefix15 * bMatrix = pc1Prefix16 := by decide +kernel
private def pc1Prefix17 : M := !![ofCode 3, ofCode 2, ofCode 6, ofCode 2; ofCode 2, ofCode 1, ofCode 6, ofCode 3; ofCode 5, ofCode 4, ofCode 7, ofCode 6; ofCode 3, ofCode 0, ofCode 4, ofCode 5]
private theorem pc1Step17 : pc1Prefix16 * cMatrix = pc1Prefix17 := by decide +kernel
private def pc1Prefix18 : M := !![ofCode 3, ofCode 7, ofCode 5, ofCode 2; ofCode 2, ofCode 7, ofCode 5, ofCode 5; ofCode 5, ofCode 0, ofCode 7, ofCode 7; ofCode 3, ofCode 5, ofCode 2, ofCode 3]
private theorem pc1Step18 : pc1Prefix17 * bInverse = pc1Prefix18 := by decide +kernel
private def pc1Prefix19 : M := !![ofCode 2, ofCode 5, ofCode 7, ofCode 3; ofCode 5, ofCode 5, ofCode 7, ofCode 2; ofCode 7, ofCode 7, ofCode 0, ofCode 5; ofCode 3, ofCode 2, ofCode 5, ofCode 3]
private theorem pc1Step19 : pc1Prefix18 * cMatrix = pc1Prefix19 := by decide +kernel
private def pc1Prefix20 : M := !![ofCode 2, ofCode 3, ofCode 1, ofCode 7; ofCode 5, ofCode 1, ofCode 1, ofCode 2; ofCode 7, ofCode 5, ofCode 3, ofCode 4; ofCode 3, ofCode 7, ofCode 0, ofCode 2]
private theorem pc1Step20 : pc1Prefix19 * bMatrix = pc1Prefix20 := by decide +kernel
private def pc1Prefix21 : M := !![ofCode 7, ofCode 1, ofCode 3, ofCode 2; ofCode 2, ofCode 1, ofCode 1, ofCode 5; ofCode 4, ofCode 3, ofCode 5, ofCode 7; ofCode 2, ofCode 0, ofCode 7, ofCode 3]
private theorem pc1Step21 : pc1Prefix20 * cMatrix = pc1Prefix21 := by decide +kernel
private def pc1Prefix22 : M := !![ofCode 7, ofCode 3, ofCode 1, ofCode 3; ofCode 2, ofCode 7, ofCode 2, ofCode 1; ofCode 4, ofCode 4, ofCode 4, ofCode 6; ofCode 2, ofCode 6, ofCode 3, ofCode 6]
private theorem pc1Step22 : pc1Prefix21 * bInverse = pc1Prefix22 := by decide +kernel
private def pc1Prefix23 : M := !![ofCode 3, ofCode 1, ofCode 3, ofCode 7; ofCode 1, ofCode 2, ofCode 7, ofCode 2; ofCode 6, ofCode 4, ofCode 4, ofCode 4; ofCode 6, ofCode 3, ofCode 6, ofCode 2]
private theorem pc1Step23 : pc1Prefix22 * cMatrix = pc1Prefix23 := by decide +kernel
private def pc1Prefix24 : M := !![ofCode 3, ofCode 4, ofCode 2, ofCode 3; ofCode 1, ofCode 1, ofCode 0, ofCode 6; ofCode 6, ofCode 5, ofCode 2, ofCode 1; ofCode 6, ofCode 2, ofCode 3, ofCode 1]
private theorem pc1Step24 : pc1Prefix23 * bInverse = pc1Prefix24 := by decide +kernel
private def pc1Prefix25 : M := !![ofCode 3, ofCode 2, ofCode 4, ofCode 3; ofCode 6, ofCode 0, ofCode 1, ofCode 1; ofCode 1, ofCode 2, ofCode 5, ofCode 6; ofCode 1, ofCode 3, ofCode 2, ofCode 6]
private theorem pc1Step25 : pc1Prefix24 * cMatrix = pc1Prefix25 := by decide +kernel
private def pc1Prefix26 : M := !![ofCode 3, ofCode 7, ofCode 1, ofCode 1; ofCode 6, ofCode 1, ofCode 1, ofCode 0; ofCode 1, ofCode 1, ofCode 0, ofCode 0; ofCode 1, ofCode 0, ofCode 0, ofCode 0]
private theorem pc1Step26 : pc1Prefix25 * bMatrix = pc1Prefix26 := by decide +kernel
private def pc1Prefix27 : M := !![ofCode 1, ofCode 1, ofCode 7, ofCode 3; ofCode 0, ofCode 1, ofCode 1, ofCode 6; ofCode 0, ofCode 0, ofCode 1, ofCode 1; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem pc1Step27 : pc1Prefix26 * cMatrix = pc1Prefix27 := by decide +kernel
private theorem pc1Step28 : pc1Prefix27 * bMatrix = pc1Matrix := by decide +kernel

theorem pc1_from_cb : b * c * b * b * c * b⁻¹ * c * b * b * c * b * c * b⁻¹ * c * b⁻¹ * c * b * c * b⁻¹ * c * b * c * b⁻¹ * c * b⁻¹ * c * b * c * b = pc1 := by
  apply Units.ext
  change bMatrix * cMatrix * bMatrix * bMatrix * cMatrix * bInverse * cMatrix * bMatrix * bMatrix * cMatrix * bMatrix * cMatrix * bInverse * cMatrix * bInverse * cMatrix * bMatrix * cMatrix * bInverse * cMatrix * bMatrix * cMatrix * bInverse * cMatrix * bInverse * cMatrix * bMatrix * cMatrix * bMatrix = pc1Matrix
  rw [pc1Step1, pc1Step2, pc1Step3, pc1Step4, pc1Step5, pc1Step6, pc1Step7, pc1Step8, pc1Step9, pc1Step10, pc1Step11, pc1Step12, pc1Step13, pc1Step14, pc1Step15, pc1Step16, pc1Step17, pc1Step18, pc1Step19, pc1Step20, pc1Step21, pc1Step22, pc1Step23, pc1Step24, pc1Step25, pc1Step26, pc1Step27, pc1Step28]

private def pc2Prefix1 : M := !![ofCode 1, ofCode 0, ofCode 2, ofCode 6; ofCode 0, ofCode 1, ofCode 0, ofCode 2; ofCode 0, ofCode 0, ofCode 1, ofCode 0; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem pc2Step1 : bMatrix * bMatrix = pc2Prefix1 := by decide +kernel
private def pc2Prefix2 : M := !![ofCode 6, ofCode 2, ofCode 0, ofCode 1; ofCode 2, ofCode 0, ofCode 1, ofCode 0; ofCode 0, ofCode 1, ofCode 0, ofCode 0; ofCode 1, ofCode 0, ofCode 0, ofCode 0]
private theorem pc2Step2 : pc2Prefix1 * cMatrix = pc2Prefix2 := by decide +kernel
private def pc2Prefix3 : M := !![ofCode 6, ofCode 3, ofCode 5, ofCode 7; ofCode 2, ofCode 6, ofCode 1, ofCode 4; ofCode 0, ofCode 1, ofCode 7, ofCode 2; ofCode 1, ofCode 3, ofCode 0, ofCode 6]
private theorem pc2Step3 : pc2Prefix2 * bMatrix = pc2Prefix3 := by decide +kernel
private def pc2Prefix4 : M := !![ofCode 6, ofCode 2, ofCode 7, ofCode 7; ofCode 2, ofCode 0, ofCode 5, ofCode 7; ofCode 0, ofCode 1, ofCode 0, ofCode 2; ofCode 1, ofCode 0, ofCode 2, ofCode 6]
private theorem pc2Step4 : pc2Prefix3 * bMatrix = pc2Prefix4 := by decide +kernel
private def pc2Prefix5 : M := !![ofCode 7, ofCode 7, ofCode 2, ofCode 6; ofCode 7, ofCode 5, ofCode 0, ofCode 2; ofCode 2, ofCode 0, ofCode 1, ofCode 0; ofCode 6, ofCode 2, ofCode 0, ofCode 1]
private theorem pc2Step5 : pc2Prefix4 * cMatrix = pc2Prefix5 := by decide +kernel
private def pc2Prefix6 : M := !![ofCode 7, ofCode 5, ofCode 1, ofCode 1; ofCode 7, ofCode 7, ofCode 6, ofCode 7; ofCode 2, ofCode 6, ofCode 1, ofCode 4; ofCode 6, ofCode 3, ofCode 5, ofCode 7]
private theorem pc2Step6 : pc2Prefix5 * bMatrix = pc2Prefix6 := by decide +kernel
private def pc2Prefix7 : M := !![ofCode 7, ofCode 7, ofCode 7, ofCode 7; ofCode 7, ofCode 5, ofCode 5, ofCode 7; ofCode 2, ofCode 0, ofCode 5, ofCode 7; ofCode 6, ofCode 2, ofCode 7, ofCode 7]
private theorem pc2Step7 : pc2Prefix6 * bMatrix = pc2Prefix7 := by decide +kernel
private def pc2Prefix8 : M := !![ofCode 7, ofCode 7, ofCode 7, ofCode 7; ofCode 7, ofCode 5, ofCode 5, ofCode 7; ofCode 7, ofCode 5, ofCode 0, ofCode 2; ofCode 7, ofCode 7, ofCode 2, ofCode 6]
private theorem pc2Step8 : pc2Prefix7 * cMatrix = pc2Prefix8 := by decide +kernel
private def pc2Prefix9 : M := !![ofCode 7, ofCode 5, ofCode 4, ofCode 4; ofCode 7, ofCode 7, ofCode 3, ofCode 6; ofCode 7, ofCode 7, ofCode 6, ofCode 7; ofCode 7, ofCode 5, ofCode 1, ofCode 1]
private theorem pc2Step9 : pc2Prefix8 * bMatrix = pc2Prefix9 := by decide +kernel
private def pc2Prefix10 : M := !![ofCode 4, ofCode 4, ofCode 5, ofCode 7; ofCode 6, ofCode 3, ofCode 7, ofCode 7; ofCode 7, ofCode 6, ofCode 7, ofCode 7; ofCode 1, ofCode 1, ofCode 5, ofCode 7]
private theorem pc2Step10 : pc2Prefix9 * cMatrix = pc2Prefix10 := by decide +kernel
private def pc2Prefix11 : M := !![ofCode 4, ofCode 3, ofCode 4, ofCode 5; ofCode 6, ofCode 2, ofCode 5, ofCode 1; ofCode 7, ofCode 4, ofCode 3, ofCode 6; ofCode 1, ofCode 2, ofCode 2, ofCode 7]
private theorem pc2Step11 : pc2Prefix10 * bMatrix = pc2Prefix11 := by decide +kernel
private def pc2Prefix12 : M := !![ofCode 4, ofCode 4, ofCode 6, ofCode 1; ofCode 6, ofCode 3, ofCode 0, ofCode 3; ofCode 7, ofCode 6, ofCode 2, ofCode 4; ofCode 1, ofCode 1, ofCode 7, ofCode 3]
private theorem pc2Step12 : pc2Prefix11 * bMatrix = pc2Prefix12 := by decide +kernel
private def pc2Prefix13 : M := !![ofCode 1, ofCode 6, ofCode 4, ofCode 4; ofCode 3, ofCode 0, ofCode 3, ofCode 6; ofCode 4, ofCode 2, ofCode 6, ofCode 7; ofCode 3, ofCode 7, ofCode 1, ofCode 1]
private theorem pc2Step13 : pc2Prefix12 * cMatrix = pc2Prefix13 := by decide +kernel
private def pc2Prefix14 : M := !![ofCode 1, ofCode 5, ofCode 0, ofCode 2; ofCode 3, ofCode 5, ofCode 3, ofCode 2; ofCode 4, ofCode 5, ofCode 3, ofCode 7; ofCode 3, ofCode 2, ofCode 2, ofCode 6]
private theorem pc2Step14 : pc2Prefix13 * bMatrix = pc2Prefix14 := by decide +kernel
private def pc2Prefix15 : M := !![ofCode 1, ofCode 6, ofCode 6, ofCode 5; ofCode 3, ofCode 0, ofCode 5, ofCode 7; ofCode 4, ofCode 2, ofCode 5, ofCode 6; ofCode 3, ofCode 7, ofCode 7, ofCode 5]
private theorem pc2Step15 : pc2Prefix14 * bMatrix = pc2Prefix15 := by decide +kernel
private def pc2Prefix16 : M := !![ofCode 5, ofCode 6, ofCode 6, ofCode 1; ofCode 7, ofCode 5, ofCode 0, ofCode 3; ofCode 6, ofCode 5, ofCode 2, ofCode 4; ofCode 5, ofCode 7, ofCode 7, ofCode 3]
private theorem pc2Step16 : pc2Prefix15 * cMatrix = pc2Prefix16 := by decide +kernel
private def pc2Prefix17 : M := !![ofCode 5, ofCode 2, ofCode 2, ofCode 4; ofCode 7, ofCode 7, ofCode 6, ofCode 6; ofCode 6, ofCode 4, ofCode 4, ofCode 1; ofCode 5, ofCode 3, ofCode 4, ofCode 7]
private theorem pc2Step17 : pc2Prefix16 * bMatrix = pc2Prefix17 := by decide +kernel
private def pc2Prefix18 : M := !![ofCode 4, ofCode 2, ofCode 2, ofCode 5; ofCode 6, ofCode 6, ofCode 7, ofCode 7; ofCode 1, ofCode 4, ofCode 4, ofCode 6; ofCode 7, ofCode 4, ofCode 3, ofCode 5]
private theorem pc2Step18 : pc2Prefix17 * cMatrix = pc2Prefix18 := by decide +kernel
private def pc2Prefix19 : M := !![ofCode 4, ofCode 5, ofCode 4, ofCode 6; ofCode 6, ofCode 7, ofCode 4, ofCode 7; ofCode 1, ofCode 7, ofCode 7, ofCode 7; ofCode 7, ofCode 6, ofCode 7, ofCode 4]
private theorem pc2Step19 : pc2Prefix18 * bInverse = pc2Prefix19 := by decide +kernel
private def pc2Prefix20 : M := !![ofCode 6, ofCode 4, ofCode 5, ofCode 4; ofCode 7, ofCode 4, ofCode 7, ofCode 6; ofCode 7, ofCode 7, ofCode 7, ofCode 1; ofCode 4, ofCode 7, ofCode 6, ofCode 7]
private theorem pc2Step20 : pc2Prefix19 * cMatrix = pc2Prefix20 := by decide +kernel
private def pc2Prefix21 : M := !![ofCode 6, ofCode 5, ofCode 4, ofCode 1; ofCode 7, ofCode 6, ofCode 6, ofCode 3; ofCode 7, ofCode 5, ofCode 4, ofCode 2; ofCode 4, ofCode 0, ofCode 5, ofCode 6]
private theorem pc2Step21 : pc2Prefix20 * bMatrix = pc2Prefix21 := by decide +kernel
private def pc2Prefix22 : M := !![ofCode 1, ofCode 4, ofCode 5, ofCode 6; ofCode 3, ofCode 6, ofCode 6, ofCode 7; ofCode 2, ofCode 4, ofCode 5, ofCode 7; ofCode 6, ofCode 5, ofCode 0, ofCode 4]
private theorem pc2Step22 : pc2Prefix21 * cMatrix = pc2Prefix22 := by decide +kernel
private def pc2Prefix23 : M := !![ofCode 1, ofCode 7, ofCode 6, ofCode 4; ofCode 3, ofCode 3, ofCode 4, ofCode 7; ofCode 2, ofCode 2, ofCode 0, ofCode 4; ofCode 6, ofCode 4, ofCode 1, ofCode 6]
private theorem pc2Step23 : pc2Prefix22 * bInverse = pc2Prefix23 := by decide +kernel
private def pc2Prefix24 : M := !![ofCode 4, ofCode 6, ofCode 7, ofCode 1; ofCode 7, ofCode 4, ofCode 3, ofCode 3; ofCode 4, ofCode 0, ofCode 2, ofCode 2; ofCode 6, ofCode 1, ofCode 4, ofCode 6]
private theorem pc2Step24 : pc2Prefix23 * cMatrix = pc2Prefix24 := by decide +kernel
private def pc2Prefix25 : M := !![ofCode 4, ofCode 1, ofCode 3, ofCode 1; ofCode 7, ofCode 6, ofCode 2, ofCode 1; ofCode 4, ofCode 7, ofCode 2, ofCode 1; ofCode 6, ofCode 0, ofCode 3, ofCode 1]
private theorem pc2Step25 : pc2Prefix24 * bMatrix = pc2Prefix25 := by decide +kernel
private def pc2Prefix26 : M := !![ofCode 1, ofCode 3, ofCode 1, ofCode 4; ofCode 1, ofCode 2, ofCode 6, ofCode 7; ofCode 1, ofCode 2, ofCode 7, ofCode 4; ofCode 1, ofCode 3, ofCode 0, ofCode 6]
private theorem pc2Step26 : pc2Prefix25 * cMatrix = pc2Prefix26 := by decide +kernel
private def pc2Prefix27 : M := !![ofCode 1, ofCode 0, ofCode 1, ofCode 1; ofCode 1, ofCode 1, ofCode 1, ofCode 0; ofCode 1, ofCode 1, ofCode 0, ofCode 0; ofCode 1, ofCode 0, ofCode 0, ofCode 0]
private theorem pc2Step27 : pc2Prefix26 * bInverse = pc2Prefix27 := by decide +kernel
private theorem pc2Step28 : pc2Prefix27 * cMatrix = pc2Matrix := by decide +kernel

theorem pc2_from_cb : b * b * c * b * b * c * b * b * c * b * c * b * b * c * b * b * c * b * c * b⁻¹ * c * b * c * b⁻¹ * c * b * c * b⁻¹ * c = pc2 := by
  apply Units.ext
  change bMatrix * bMatrix * cMatrix * bMatrix * bMatrix * cMatrix * bMatrix * bMatrix * cMatrix * bMatrix * cMatrix * bMatrix * bMatrix * cMatrix * bMatrix * bMatrix * cMatrix * bMatrix * cMatrix * bInverse * cMatrix * bMatrix * cMatrix * bInverse * cMatrix * bMatrix * cMatrix * bInverse * cMatrix = pc2Matrix
  rw [pc2Step1, pc2Step2, pc2Step3, pc2Step4, pc2Step5, pc2Step6, pc2Step7, pc2Step8, pc2Step9, pc2Step10, pc2Step11, pc2Step12, pc2Step13, pc2Step14, pc2Step15, pc2Step16, pc2Step17, pc2Step18, pc2Step19, pc2Step20, pc2Step21, pc2Step22, pc2Step23, pc2Step24, pc2Step25, pc2Step26, pc2Step27, pc2Step28]

private def pc3Prefix1 : M := !![ofCode 6, ofCode 0, ofCode 3, ofCode 1; ofCode 2, ofCode 7, ofCode 1, ofCode 0; ofCode 3, ofCode 1, ofCode 0, ofCode 0; ofCode 1, ofCode 0, ofCode 0, ofCode 0]
private theorem pc3Step1 : bMatrix * cMatrix = pc3Prefix1 := by decide +kernel
private def pc3Prefix2 : M := !![ofCode 6, ofCode 1, ofCode 3, ofCode 6; ofCode 2, ofCode 1, ofCode 2, ofCode 1; ofCode 3, ofCode 4, ofCode 7, ofCode 3; ofCode 1, ofCode 3, ofCode 0, ofCode 6]
private theorem pc3Step2 : pc3Prefix1 * bMatrix = pc3Prefix2 := by decide +kernel
private def pc3Prefix3 : M := !![ofCode 6, ofCode 3, ofCode 1, ofCode 6; ofCode 1, ofCode 2, ofCode 1, ofCode 2; ofCode 3, ofCode 7, ofCode 4, ofCode 3; ofCode 6, ofCode 0, ofCode 3, ofCode 1]
private theorem pc3Step3 : pc3Prefix2 * cMatrix = pc3Prefix3 := by decide +kernel
private def pc3Prefix4 : M := !![ofCode 6, ofCode 2, ofCode 4, ofCode 7; ofCode 1, ofCode 1, ofCode 6, ofCode 7; ofCode 3, ofCode 2, ofCode 1, ofCode 5; ofCode 6, ofCode 1, ofCode 4, ofCode 6]
private theorem pc3Step4 : pc3Prefix3 * bInverse = pc3Prefix4 := by decide +kernel
private def pc3Prefix5 : M := !![ofCode 7, ofCode 4, ofCode 2, ofCode 6; ofCode 7, ofCode 6, ofCode 1, ofCode 1; ofCode 5, ofCode 1, ofCode 2, ofCode 3; ofCode 6, ofCode 4, ofCode 1, ofCode 6]
private theorem pc3Step5 : pc3Prefix4 * cMatrix = pc3Prefix5 := by decide +kernel
private def pc3Prefix6 : M := !![ofCode 7, ofCode 6, ofCode 3, ofCode 7; ofCode 7, ofCode 4, ofCode 5, ofCode 1; ofCode 5, ofCode 5, ofCode 5, ofCode 4; ofCode 6, ofCode 5, ofCode 0, ofCode 4]
private theorem pc3Step6 : pc3Prefix5 * bMatrix = pc3Prefix6 := by decide +kernel
private def pc3Prefix7 : M := !![ofCode 7, ofCode 4, ofCode 7, ofCode 1; ofCode 7, ofCode 6, ofCode 4, ofCode 2; ofCode 5, ofCode 1, ofCode 3, ofCode 2; ofCode 6, ofCode 4, ofCode 6, ofCode 7]
private theorem pc3Step7 : pc3Prefix6 * bMatrix = pc3Prefix7 := by decide +kernel
private def pc3Prefix8 : M := !![ofCode 1, ofCode 7, ofCode 4, ofCode 7; ofCode 2, ofCode 4, ofCode 6, ofCode 7; ofCode 2, ofCode 3, ofCode 1, ofCode 5; ofCode 7, ofCode 6, ofCode 4, ofCode 6]
private theorem pc3Step8 : pc3Prefix7 * cMatrix = pc3Prefix8 := by decide +kernel
private def pc3Prefix9 : M := !![ofCode 1, ofCode 4, ofCode 5, ofCode 6; ofCode 2, ofCode 2, ofCode 3, ofCode 1; ofCode 2, ofCode 5, ofCode 7, ofCode 1; ofCode 7, ofCode 4, ofCode 5, ofCode 5]
private theorem pc3Step9 : pc3Prefix8 * bInverse = pc3Prefix9 := by decide +kernel
private def pc3Prefix10 : M := !![ofCode 6, ofCode 5, ofCode 4, ofCode 1; ofCode 1, ofCode 3, ofCode 2, ofCode 2; ofCode 1, ofCode 7, ofCode 5, ofCode 2; ofCode 5, ofCode 5, ofCode 4, ofCode 7]
private theorem pc3Step10 : pc3Prefix9 * cMatrix = pc3Prefix10 := by decide +kernel
private def pc3Prefix11 : M := !![ofCode 6, ofCode 4, ofCode 2, ofCode 5; ofCode 1, ofCode 0, ofCode 0, ofCode 4; ofCode 1, ofCode 4, ofCode 6, ofCode 5; ofCode 5, ofCode 1, ofCode 2, ofCode 2]
private theorem pc3Step11 : pc3Prefix10 * bMatrix = pc3Prefix11 := by decide +kernel
private def pc3Prefix12 : M := !![ofCode 6, ofCode 5, ofCode 3, ofCode 2; ofCode 1, ofCode 3, ofCode 0, ofCode 2; ofCode 1, ofCode 7, ofCode 7, ofCode 1; ofCode 5, ofCode 5, ofCode 5, ofCode 5]
private theorem pc3Step12 : pc3Prefix11 * bMatrix = pc3Prefix12 := by decide +kernel
private def pc3Prefix13 : M := !![ofCode 2, ofCode 3, ofCode 5, ofCode 6; ofCode 2, ofCode 0, ofCode 3, ofCode 1; ofCode 1, ofCode 7, ofCode 7, ofCode 1; ofCode 5, ofCode 5, ofCode 5, ofCode 5]
private theorem pc3Step13 : pc3Prefix12 * cMatrix = pc3Prefix13 := by decide +kernel
private def pc3Prefix14 : M := !![ofCode 2, ofCode 5, ofCode 7, ofCode 3; ofCode 2, ofCode 6, ofCode 3, ofCode 3; ofCode 1, ofCode 4, ofCode 4, ofCode 0; ofCode 5, ofCode 1, ofCode 3, ofCode 3]
private theorem pc3Step14 : pc3Prefix13 * bMatrix = pc3Prefix14 := by decide +kernel
private def pc3Prefix15 : M := !![ofCode 3, ofCode 7, ofCode 5, ofCode 2; ofCode 3, ofCode 3, ofCode 6, ofCode 2; ofCode 0, ofCode 4, ofCode 4, ofCode 1; ofCode 3, ofCode 3, ofCode 1, ofCode 5]
private theorem pc3Step15 : pc3Prefix14 * cMatrix = pc3Prefix15 := by decide +kernel
private def pc3Prefix16 : M := !![ofCode 3, ofCode 2, ofCode 0, ofCode 7; ofCode 3, ofCode 6, ofCode 2, ofCode 2; ofCode 0, ofCode 4, ofCode 5, ofCode 6; ofCode 3, ofCode 6, ofCode 5, ofCode 7]
private theorem pc3Step16 : pc3Prefix15 * bInverse = pc3Prefix16 := by decide +kernel
private def pc3Prefix17 : M := !![ofCode 7, ofCode 0, ofCode 2, ofCode 3; ofCode 2, ofCode 2, ofCode 6, ofCode 3; ofCode 6, ofCode 5, ofCode 4, ofCode 0; ofCode 7, ofCode 5, ofCode 6, ofCode 3]
private theorem pc3Step17 : pc3Prefix16 * cMatrix = pc3Prefix17 := by decide +kernel
private def pc3Prefix18 : M := !![ofCode 7, ofCode 2, ofCode 2, ofCode 1; ofCode 2, ofCode 4, ofCode 3, ofCode 1; ofCode 6, ofCode 4, ofCode 2, ofCode 4; ofCode 7, ofCode 7, ofCode 0, ofCode 7]
private theorem pc3Step18 : pc3Prefix17 * bMatrix = pc3Prefix18 := by decide +kernel
private def pc3Prefix19 : M := !![ofCode 7, ofCode 0, ofCode 7, ofCode 7; ofCode 2, ofCode 2, ofCode 2, ofCode 0; ofCode 6, ofCode 5, ofCode 3, ofCode 3; ofCode 7, ofCode 5, ofCode 3, ofCode 6]
private theorem pc3Step19 : pc3Prefix18 * bMatrix = pc3Prefix19 := by decide +kernel
private def pc3Prefix20 : M := !![ofCode 7, ofCode 7, ofCode 0, ofCode 7; ofCode 0, ofCode 2, ofCode 2, ofCode 2; ofCode 3, ofCode 3, ofCode 5, ofCode 6; ofCode 6, ofCode 3, ofCode 5, ofCode 7]
private theorem pc3Step20 : pc3Prefix19 * cMatrix = pc3Prefix20 := by decide +kernel
private def pc3Prefix21 : M := !![ofCode 7, ofCode 5, ofCode 6, ofCode 3; ofCode 0, ofCode 2, ofCode 7, ofCode 4; ofCode 3, ofCode 6, ofCode 1, ofCode 3; ofCode 6, ofCode 2, ofCode 0, ofCode 1]
private theorem pc3Step21 : pc3Prefix20 * bInverse = pc3Prefix21 := by decide +kernel
private def pc3Prefix22 : M := !![ofCode 3, ofCode 6, ofCode 5, ofCode 7; ofCode 4, ofCode 7, ofCode 2, ofCode 0; ofCode 3, ofCode 1, ofCode 6, ofCode 3; ofCode 1, ofCode 0, ofCode 2, ofCode 6]
private theorem pc3Step22 : pc3Prefix21 * cMatrix = pc3Prefix22 := by decide +kernel
private def pc3Prefix23 : M := !![ofCode 3, ofCode 3, ofCode 1, ofCode 5; ofCode 4, ofCode 0, ofCode 1, ofCode 6; ofCode 3, ofCode 4, ofCode 1, ofCode 1; ofCode 1, ofCode 3, ofCode 2, ofCode 6]
private theorem pc3Step23 : pc3Prefix22 * bMatrix = pc3Prefix23 := by decide +kernel
private def pc3Prefix24 : M := !![ofCode 3, ofCode 6, ofCode 3, ofCode 1; ofCode 4, ofCode 7, ofCode 1, ofCode 0; ofCode 3, ofCode 1, ofCode 0, ofCode 0; ofCode 1, ofCode 0, ofCode 0, ofCode 0]
private theorem pc3Step24 : pc3Prefix23 * bMatrix = pc3Prefix24 := by decide +kernel
private def pc3Prefix25 : M := !![ofCode 1, ofCode 3, ofCode 6, ofCode 3; ofCode 0, ofCode 1, ofCode 7, ofCode 4; ofCode 0, ofCode 0, ofCode 1, ofCode 3; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem pc3Step25 : pc3Prefix24 * cMatrix = pc3Prefix25 := by decide +kernel
private theorem pc3Step26 : pc3Prefix25 * bMatrix = pc3Matrix := by decide +kernel

theorem pc3_from_cb : b * c * b * c * b⁻¹ * c * b * b * c * b⁻¹ * c * b * b * c * b * c * b⁻¹ * c * b * b * c * b⁻¹ * c * b * b * c * b = pc3 := by
  apply Units.ext
  change bMatrix * cMatrix * bMatrix * cMatrix * bInverse * cMatrix * bMatrix * bMatrix * cMatrix * bInverse * cMatrix * bMatrix * bMatrix * cMatrix * bMatrix * cMatrix * bInverse * cMatrix * bMatrix * bMatrix * cMatrix * bInverse * cMatrix * bMatrix * bMatrix * cMatrix * bMatrix = pc3Matrix
  rw [pc3Step1, pc3Step2, pc3Step3, pc3Step4, pc3Step5, pc3Step6, pc3Step7, pc3Step8, pc3Step9, pc3Step10, pc3Step11, pc3Step12, pc3Step13, pc3Step14, pc3Step15, pc3Step16, pc3Step17, pc3Step18, pc3Step19, pc3Step20, pc3Step21, pc3Step22, pc3Step23, pc3Step24, pc3Step25, pc3Step26]

private theorem pc4Step1 : bMatrix * bMatrix = pc4Matrix := by decide +kernel

theorem pc4_from_cb : b * b = pc4 := by
  apply Units.ext
  change bMatrix * bMatrix = pc4Matrix
  rw [pc4Step1]

private def pc5Prefix1 : M := !![ofCode 0, ofCode 0, ofCode 0, ofCode 1; ofCode 0, ofCode 0, ofCode 1, ofCode 3; ofCode 0, ofCode 1, ofCode 7, ofCode 0; ofCode 1, ofCode 3, ofCode 2, ofCode 6]
private theorem pc5Step1 : cMatrix * bInverse = pc5Prefix1 := by decide +kernel
private def pc5Prefix2 : M := !![ofCode 1, ofCode 0, ofCode 0, ofCode 0; ofCode 3, ofCode 1, ofCode 0, ofCode 0; ofCode 0, ofCode 7, ofCode 1, ofCode 0; ofCode 6, ofCode 2, ofCode 3, ofCode 1]
private theorem pc5Step2 : pc5Prefix1 * cMatrix = pc5Prefix2 := by decide +kernel
private def pc5Prefix3 : M := !![ofCode 1, ofCode 3, ofCode 0, ofCode 6; ofCode 3, ofCode 4, ofCode 7, ofCode 3; ofCode 0, ofCode 7, ofCode 2, ofCode 6; ofCode 6, ofCode 3, ofCode 6, ofCode 2]
private theorem pc5Step3 : pc5Prefix2 * bMatrix = pc5Prefix3 := by decide +kernel
private def pc5Prefix4 : M := !![ofCode 6, ofCode 0, ofCode 3, ofCode 1; ofCode 3, ofCode 7, ofCode 4, ofCode 3; ofCode 6, ofCode 2, ofCode 7, ofCode 0; ofCode 2, ofCode 6, ofCode 3, ofCode 6]
private theorem pc5Step4 : pc5Prefix3 * cMatrix = pc5Prefix4 := by decide +kernel
private def pc5Prefix5 : M := !![ofCode 6, ofCode 1, ofCode 3, ofCode 6; ofCode 3, ofCode 2, ofCode 7, ofCode 0; ofCode 6, ofCode 3, ofCode 2, ofCode 4; ofCode 2, ofCode 0, ofCode 7, ofCode 3]
private theorem pc5Step5 : pc5Prefix4 * bMatrix = pc5Prefix5 := by decide +kernel
private def pc5Prefix6 : M := !![ofCode 6, ofCode 0, ofCode 4, ofCode 3; ofCode 3, ofCode 7, ofCode 2, ofCode 7; ofCode 6, ofCode 2, ofCode 0, ofCode 6; ofCode 2, ofCode 6, ofCode 7, ofCode 6]
private theorem pc5Step6 : pc5Prefix5 * bMatrix = pc5Prefix6 := by decide +kernel
private def pc5Prefix7 : M := !![ofCode 3, ofCode 4, ofCode 0, ofCode 6; ofCode 7, ofCode 2, ofCode 7, ofCode 3; ofCode 6, ofCode 0, ofCode 2, ofCode 6; ofCode 6, ofCode 7, ofCode 6, ofCode 2]
private theorem pc5Step7 : pc5Prefix6 * cMatrix = pc5Prefix7 := by decide +kernel
private def pc5Prefix8 : M := !![ofCode 3, ofCode 1, ofCode 7, ofCode 7; ofCode 7, ofCode 0, ofCode 7, ofCode 5; ofCode 6, ofCode 1, ofCode 5, ofCode 2; ofCode 6, ofCode 6, ofCode 2, ofCode 1]
private theorem pc5Step8 : pc5Prefix7 * bInverse = pc5Prefix8 := by decide +kernel
private def pc5Prefix9 : M := !![ofCode 7, ofCode 7, ofCode 1, ofCode 3; ofCode 5, ofCode 7, ofCode 0, ofCode 7; ofCode 2, ofCode 5, ofCode 1, ofCode 6; ofCode 1, ofCode 2, ofCode 6, ofCode 6]
private theorem pc5Step9 : pc5Prefix8 * cMatrix = pc5Prefix9 := by decide +kernel
private def pc5Prefix10 : M := !![ofCode 7, ofCode 5, ofCode 2, ofCode 1; ofCode 5, ofCode 3, ofCode 3, ofCode 1; ofCode 2, ofCode 3, ofCode 7, ofCode 3; ofCode 1, ofCode 1, ofCode 3, ofCode 5]
private theorem pc5Step10 : pc5Prefix9 * bMatrix = pc5Prefix10 := by decide +kernel
private def pc5Prefix11 : M := !![ofCode 7, ofCode 7, ofCode 4, ofCode 2; ofCode 5, ofCode 7, ofCode 1, ofCode 1; ofCode 2, ofCode 5, ofCode 5, ofCode 0; ofCode 1, ofCode 2, ofCode 4, ofCode 4]
private theorem pc5Step11 : pc5Prefix10 * bMatrix = pc5Prefix11 := by decide +kernel
private def pc5Prefix12 : M := !![ofCode 2, ofCode 4, ofCode 7, ofCode 7; ofCode 1, ofCode 1, ofCode 7, ofCode 5; ofCode 0, ofCode 5, ofCode 5, ofCode 2; ofCode 4, ofCode 4, ofCode 2, ofCode 1]
private theorem pc5Step12 : pc5Prefix11 * cMatrix = pc5Prefix12 := by decide +kernel
private def pc5Prefix13 : M := !![ofCode 2, ofCode 2, ofCode 2, ofCode 2; ofCode 1, ofCode 2, ofCode 2, ofCode 1; ofCode 0, ofCode 5, ofCode 3, ofCode 6; ofCode 4, ofCode 3, ofCode 0, ofCode 2]
private theorem pc5Step13 : pc5Prefix12 * bInverse = pc5Prefix13 := by decide +kernel
private def pc5Prefix14 : M := !![ofCode 2, ofCode 2, ofCode 2, ofCode 2; ofCode 1, ofCode 2, ofCode 2, ofCode 1; ofCode 6, ofCode 3, ofCode 5, ofCode 0; ofCode 2, ofCode 0, ofCode 3, ofCode 4]
private theorem pc5Step14 : pc5Prefix13 * cMatrix = pc5Prefix14 := by decide +kernel
private def pc5Prefix15 : M := !![ofCode 2, ofCode 4, ofCode 7, ofCode 7; ofCode 1, ofCode 1, ofCode 7, ofCode 5; ofCode 6, ofCode 2, ofCode 7, ofCode 0; ofCode 2, ofCode 6, ofCode 3, ofCode 6]
private theorem pc5Step15 : pc5Prefix14 * bMatrix = pc5Prefix15 := by decide +kernel
private def pc5Prefix16 : M := !![ofCode 7, ofCode 7, ofCode 4, ofCode 2; ofCode 5, ofCode 7, ofCode 1, ofCode 1; ofCode 0, ofCode 7, ofCode 2, ofCode 6; ofCode 6, ofCode 3, ofCode 6, ofCode 2]
private theorem pc5Step16 : pc5Prefix15 * cMatrix = pc5Prefix16 := by decide +kernel
private def pc5Prefix17 : M := !![ofCode 7, ofCode 5, ofCode 2, ofCode 1; ofCode 5, ofCode 3, ofCode 3, ofCode 1; ofCode 0, ofCode 7, ofCode 1, ofCode 0; ofCode 6, ofCode 2, ofCode 3, ofCode 1]
private theorem pc5Step17 : pc5Prefix16 * bInverse = pc5Prefix17 := by decide +kernel
private def pc5Prefix18 : M := !![ofCode 1, ofCode 2, ofCode 5, ofCode 7; ofCode 1, ofCode 3, ofCode 3, ofCode 5; ofCode 0, ofCode 1, ofCode 7, ofCode 0; ofCode 1, ofCode 3, ofCode 2, ofCode 6]
private theorem pc5Step18 : pc5Prefix17 * cMatrix = pc5Prefix18 := by decide +kernel
private def pc5Prefix19 : M := !![ofCode 1, ofCode 1, ofCode 0, ofCode 1; ofCode 1, ofCode 0, ofCode 1, ofCode 0; ofCode 0, ofCode 1, ofCode 0, ofCode 0; ofCode 1, ofCode 0, ofCode 0, ofCode 0]
private theorem pc5Step19 : pc5Prefix18 * bMatrix = pc5Prefix19 := by decide +kernel
private theorem pc5Step20 : pc5Prefix19 * cMatrix = pc5Matrix := by decide +kernel

theorem pc5_from_cb : c * b⁻¹ * c * b * c * b * b * c * b⁻¹ * c * b * b * c * b⁻¹ * c * b * c * b⁻¹ * c * b * c = pc5 := by
  apply Units.ext
  change cMatrix * bInverse * cMatrix * bMatrix * cMatrix * bMatrix * bMatrix * cMatrix * bInverse * cMatrix * bMatrix * bMatrix * cMatrix * bInverse * cMatrix * bMatrix * cMatrix * bInverse * cMatrix * bMatrix * cMatrix = pc5Matrix
  rw [pc5Step1, pc5Step2, pc5Step3, pc5Step4, pc5Step5, pc5Step6, pc5Step7, pc5Step8, pc5Step9, pc5Step10, pc5Step11, pc5Step12, pc5Step13, pc5Step14, pc5Step15, pc5Step16, pc5Step17, pc5Step18, pc5Step19, pc5Step20]

private def pc6Prefix1 : M := !![ofCode 6, ofCode 2, ofCode 3, ofCode 1; ofCode 0, ofCode 7, ofCode 1, ofCode 0; ofCode 3, ofCode 1, ofCode 0, ofCode 0; ofCode 1, ofCode 0, ofCode 0, ofCode 0]
private theorem pc6Step1 : bInverse * cMatrix = pc6Prefix1 := by decide +kernel
private def pc6Prefix2 : M := !![ofCode 6, ofCode 3, ofCode 6, ofCode 2; ofCode 0, ofCode 7, ofCode 2, ofCode 6; ofCode 3, ofCode 4, ofCode 7, ofCode 3; ofCode 1, ofCode 3, ofCode 0, ofCode 6]
private theorem pc6Step2 : pc6Prefix1 * bMatrix = pc6Prefix2 := by decide +kernel
private def pc6Prefix3 : M := !![ofCode 2, ofCode 6, ofCode 3, ofCode 6; ofCode 6, ofCode 2, ofCode 7, ofCode 0; ofCode 3, ofCode 7, ofCode 4, ofCode 3; ofCode 6, ofCode 0, ofCode 3, ofCode 1]
private theorem pc6Step3 : pc6Prefix2 * cMatrix = pc6Prefix3 := by decide +kernel
private def pc6Prefix4 : M := !![ofCode 2, ofCode 0, ofCode 7, ofCode 3; ofCode 6, ofCode 3, ofCode 2, ofCode 4; ofCode 3, ofCode 2, ofCode 7, ofCode 0; ofCode 6, ofCode 1, ofCode 3, ofCode 6]
private theorem pc6Step4 : pc6Prefix3 * bMatrix = pc6Prefix4 := by decide +kernel
private def pc6Prefix5 : M := !![ofCode 2, ofCode 6, ofCode 7, ofCode 6; ofCode 6, ofCode 2, ofCode 0, ofCode 6; ofCode 3, ofCode 7, ofCode 2, ofCode 7; ofCode 6, ofCode 0, ofCode 4, ofCode 3]
private theorem pc6Step5 : pc6Prefix4 * bMatrix = pc6Prefix5 := by decide +kernel
private def pc6Prefix6 : M := !![ofCode 6, ofCode 7, ofCode 6, ofCode 2; ofCode 6, ofCode 0, ofCode 2, ofCode 6; ofCode 7, ofCode 2, ofCode 7, ofCode 3; ofCode 3, ofCode 4, ofCode 0, ofCode 6]
private theorem pc6Step6 : pc6Prefix5 * cMatrix = pc6Prefix6 := by decide +kernel
private def pc6Prefix7 : M := !![ofCode 6, ofCode 6, ofCode 2, ofCode 1; ofCode 6, ofCode 1, ofCode 5, ofCode 2; ofCode 7, ofCode 0, ofCode 7, ofCode 5; ofCode 3, ofCode 1, ofCode 7, ofCode 7]
private theorem pc6Step7 : pc6Prefix6 * bInverse = pc6Prefix7 := by decide +kernel
private def pc6Prefix8 : M := !![ofCode 1, ofCode 2, ofCode 6, ofCode 6; ofCode 2, ofCode 5, ofCode 1, ofCode 6; ofCode 5, ofCode 7, ofCode 0, ofCode 7; ofCode 7, ofCode 7, ofCode 1, ofCode 3]
private theorem pc6Step8 : pc6Prefix7 * cMatrix = pc6Prefix8 := by decide +kernel
private def pc6Prefix9 : M := !![ofCode 1, ofCode 1, ofCode 3, ofCode 5; ofCode 2, ofCode 3, ofCode 7, ofCode 3; ofCode 5, ofCode 3, ofCode 3, ofCode 1; ofCode 7, ofCode 5, ofCode 2, ofCode 1]
private theorem pc6Step9 : pc6Prefix8 * bMatrix = pc6Prefix9 := by decide +kernel
private def pc6Prefix10 : M := !![ofCode 5, ofCode 3, ofCode 1, ofCode 1; ofCode 3, ofCode 7, ofCode 3, ofCode 2; ofCode 1, ofCode 3, ofCode 3, ofCode 5; ofCode 1, ofCode 2, ofCode 5, ofCode 7]
private theorem pc6Step10 : pc6Prefix9 * cMatrix = pc6Prefix10 := by decide +kernel
private def pc6Prefix11 : M := !![ofCode 5, ofCode 7, ofCode 3, ofCode 7; ofCode 3, ofCode 2, ofCode 0, ofCode 3; ofCode 1, ofCode 0, ofCode 1, ofCode 0; ofCode 1, ofCode 1, ofCode 0, ofCode 1]
private theorem pc6Step11 : pc6Prefix10 * bMatrix = pc6Prefix11 := by decide +kernel
private def pc6Prefix12 : M := !![ofCode 5, ofCode 3, ofCode 0, ofCode 4; ofCode 3, ofCode 7, ofCode 5, ofCode 6; ofCode 1, ofCode 3, ofCode 1, ofCode 5; ofCode 1, ofCode 2, ofCode 7, ofCode 5]
private theorem pc6Step12 : pc6Prefix11 * bMatrix = pc6Prefix12 := by decide +kernel
private def pc6Prefix13 : M := !![ofCode 4, ofCode 0, ofCode 3, ofCode 5; ofCode 6, ofCode 5, ofCode 7, ofCode 3; ofCode 5, ofCode 1, ofCode 3, ofCode 1; ofCode 5, ofCode 7, ofCode 2, ofCode 1]
private theorem pc6Step13 : pc6Prefix12 * cMatrix = pc6Prefix13 := by decide +kernel
private def pc6Prefix14 : M := !![ofCode 4, ofCode 7, ofCode 0, ofCode 5; ofCode 6, ofCode 4, ofCode 6, ofCode 3; ofCode 5, ofCode 5, ofCode 5, ofCode 7; ofCode 5, ofCode 3, ofCode 0, ofCode 4]
private theorem pc6Step14 : pc6Prefix13 * bInverse = pc6Prefix14 := by decide +kernel
private def pc6Prefix15 : M := !![ofCode 5, ofCode 0, ofCode 7, ofCode 4; ofCode 3, ofCode 6, ofCode 4, ofCode 6; ofCode 7, ofCode 5, ofCode 5, ofCode 5; ofCode 4, ofCode 0, ofCode 3, ofCode 5]
private theorem pc6Step15 : pc6Prefix14 * cMatrix = pc6Prefix15 := by decide +kernel
private def pc6Prefix16 : M := !![ofCode 5, ofCode 4, ofCode 7, ofCode 5; ofCode 3, ofCode 3, ofCode 0, ofCode 7; ofCode 7, ofCode 7, ofCode 3, ofCode 4; ofCode 4, ofCode 7, ofCode 3, ofCode 5]
private theorem pc6Step16 : pc6Prefix15 * bMatrix = pc6Prefix16 := by decide +kernel
private def pc6Prefix17 : M := !![ofCode 5, ofCode 7, ofCode 4, ofCode 5; ofCode 7, ofCode 0, ofCode 3, ofCode 3; ofCode 4, ofCode 3, ofCode 7, ofCode 7; ofCode 5, ofCode 3, ofCode 7, ofCode 4]
private theorem pc6Step17 : pc6Prefix16 * cMatrix = pc6Prefix17 := by decide +kernel
private def pc6Prefix18 : M := !![ofCode 5, ofCode 3, ofCode 6, ofCode 1; ofCode 7, ofCode 2, ofCode 6, ofCode 2; ofCode 4, ofCode 4, ofCode 6, ofCode 0; ofCode 5, ofCode 7, ofCode 4, ofCode 5]
private theorem pc6Step18 : pc6Prefix17 * bInverse = pc6Prefix18 := by decide +kernel
private def pc6Prefix19 : M := !![ofCode 1, ofCode 6, ofCode 3, ofCode 5; ofCode 2, ofCode 6, ofCode 2, ofCode 7; ofCode 0, ofCode 6, ofCode 4, ofCode 4; ofCode 5, ofCode 4, ofCode 7, ofCode 5]
private theorem pc6Step19 : pc6Prefix18 * cMatrix = pc6Prefix19 := by decide +kernel
private def pc6Prefix20 : M := !![ofCode 1, ofCode 5, ofCode 7, ofCode 1; ofCode 2, ofCode 0, ofCode 6, ofCode 1; ofCode 0, ofCode 6, ofCode 0, ofCode 4; ofCode 5, ofCode 0, ofCode 6, ofCode 7]
private theorem pc6Step20 : pc6Prefix19 * bMatrix = pc6Prefix20 := by decide +kernel
private def pc6Prefix21 : M := !![ofCode 1, ofCode 6, ofCode 1, ofCode 4; ofCode 2, ofCode 6, ofCode 6, ofCode 7; ofCode 0, ofCode 6, ofCode 4, ofCode 3; ofCode 5, ofCode 4, ofCode 6, ofCode 5]
private theorem pc6Step21 : pc6Prefix20 * bMatrix = pc6Prefix21 := by decide +kernel
private def pc6Prefix22 : M := !![ofCode 4, ofCode 1, ofCode 6, ofCode 1; ofCode 7, ofCode 6, ofCode 6, ofCode 2; ofCode 3, ofCode 4, ofCode 6, ofCode 0; ofCode 5, ofCode 6, ofCode 4, ofCode 5]
private theorem pc6Step22 : pc6Prefix21 * cMatrix = pc6Prefix22 := by decide +kernel
private def pc6Prefix23 : M := !![ofCode 4, ofCode 6, ofCode 1, ofCode 7; ofCode 7, ofCode 4, ofCode 2, ofCode 0; ofCode 3, ofCode 1, ofCode 7, ofCode 3; ofCode 5, ofCode 2, ofCode 0, ofCode 6]
private theorem pc6Step23 : pc6Prefix22 * bMatrix = pc6Prefix23 := by decide +kernel
private def pc6Prefix24 : M := !![ofCode 7, ofCode 1, ofCode 6, ofCode 4; ofCode 0, ofCode 2, ofCode 4, ofCode 7; ofCode 3, ofCode 7, ofCode 1, ofCode 3; ofCode 6, ofCode 0, ofCode 2, ofCode 5]
private theorem pc6Step24 : pc6Prefix23 * cMatrix = pc6Prefix24 := by decide +kernel
private def pc6Prefix25 : M := !![ofCode 7, ofCode 3, ofCode 4, ofCode 1; ofCode 0, ofCode 2, ofCode 1, ofCode 0; ofCode 3, ofCode 2, ofCode 4, ofCode 1; ofCode 6, ofCode 1, ofCode 5, ofCode 1]
private theorem pc6Step25 : pc6Prefix24 * bInverse = pc6Prefix25 := by decide +kernel
private def pc6Prefix26 : M := !![ofCode 1, ofCode 4, ofCode 3, ofCode 7; ofCode 0, ofCode 1, ofCode 2, ofCode 0; ofCode 1, ofCode 4, ofCode 2, ofCode 3; ofCode 1, ofCode 5, ofCode 1, ofCode 6]
private theorem pc6Step26 : pc6Prefix25 * cMatrix = pc6Prefix26 := by decide +kernel
private def pc6Prefix27 : M := !![ofCode 1, ofCode 7, ofCode 2, ofCode 7; ofCode 0, ofCode 1, ofCode 5, ofCode 4; ofCode 1, ofCode 7, ofCode 3, ofCode 0; ofCode 1, ofCode 6, ofCode 7, ofCode 2]
private theorem pc6Step27 : pc6Prefix26 * bMatrix = pc6Prefix27 := by decide +kernel
private def pc6Prefix28 : M := !![ofCode 7, ofCode 2, ofCode 7, ofCode 1; ofCode 4, ofCode 5, ofCode 1, ofCode 0; ofCode 0, ofCode 3, ofCode 7, ofCode 1; ofCode 2, ofCode 7, ofCode 6, ofCode 1]
private theorem pc6Step28 : pc6Prefix27 * cMatrix = pc6Prefix28 := by decide +kernel
private def pc6Prefix29 : M := !![ofCode 7, ofCode 0, ofCode 7, ofCode 7; ofCode 4, ofCode 2, ofCode 4, ofCode 6; ofCode 0, ofCode 3, ofCode 5, ofCode 3; ofCode 2, ofCode 1, ofCode 1, ofCode 7]
private theorem pc6Step29 : pc6Prefix28 * bInverse = pc6Prefix29 := by decide +kernel
private def pc6Prefix30 : M := !![ofCode 7, ofCode 7, ofCode 0, ofCode 7; ofCode 6, ofCode 4, ofCode 2, ofCode 4; ofCode 3, ofCode 5, ofCode 3, ofCode 0; ofCode 7, ofCode 1, ofCode 1, ofCode 2]
private theorem pc6Step30 : pc6Prefix29 * cMatrix = pc6Prefix30 := by decide +kernel
private def pc6Prefix31 : M := !![ofCode 7, ofCode 5, ofCode 3, ofCode 6; ofCode 6, ofCode 5, ofCode 3, ofCode 3; ofCode 3, ofCode 0, ofCode 5, ofCode 5; ofCode 7, ofCode 3, ofCode 6, ofCode 7]
private theorem pc6Step31 : pc6Prefix30 * bMatrix = pc6Prefix31 := by decide +kernel
private def pc6Prefix32 : M := !![ofCode 6, ofCode 3, ofCode 5, ofCode 7; ofCode 3, ofCode 3, ofCode 5, ofCode 6; ofCode 5, ofCode 5, ofCode 0, ofCode 3; ofCode 7, ofCode 6, ofCode 3, ofCode 7]
private theorem pc6Step32 : pc6Prefix31 * cMatrix = pc6Prefix32 := by decide +kernel
private def pc6Prefix33 : M := !![ofCode 6, ofCode 2, ofCode 0, ofCode 1; ofCode 3, ofCode 6, ofCode 1, ofCode 3; ofCode 5, ofCode 1, ofCode 7, ofCode 0; ofCode 7, ofCode 4, ofCode 2, ofCode 6]
private theorem pc6Step33 : pc6Prefix32 * bInverse = pc6Prefix33 := by decide +kernel
private def pc6Prefix34 : M := !![ofCode 1, ofCode 0, ofCode 2, ofCode 6; ofCode 3, ofCode 1, ofCode 6, ofCode 3; ofCode 0, ofCode 7, ofCode 1, ofCode 5; ofCode 6, ofCode 2, ofCode 4, ofCode 7]
private theorem pc6Step34 : pc6Prefix33 * cMatrix = pc6Prefix34 := by decide +kernel
private def pc6Prefix35 : M := !![ofCode 1, ofCode 3, ofCode 2, ofCode 6; ofCode 3, ofCode 4, ofCode 1, ofCode 1; ofCode 0, ofCode 7, ofCode 2, ofCode 3; ofCode 6, ofCode 3, ofCode 1, ofCode 6]
private theorem pc6Step35 : pc6Prefix34 * bMatrix = pc6Prefix35 := by decide +kernel
private def pc6Prefix36 : M := !![ofCode 1, ofCode 0, ofCode 0, ofCode 0; ofCode 3, ofCode 1, ofCode 0, ofCode 0; ofCode 0, ofCode 7, ofCode 1, ofCode 0; ofCode 6, ofCode 2, ofCode 3, ofCode 1]
private theorem pc6Step36 : pc6Prefix35 * bMatrix = pc6Prefix36 := by decide +kernel
private def pc6Prefix37 : M := !![ofCode 0, ofCode 0, ofCode 0, ofCode 1; ofCode 0, ofCode 0, ofCode 1, ofCode 3; ofCode 0, ofCode 1, ofCode 7, ofCode 0; ofCode 1, ofCode 3, ofCode 2, ofCode 6]
private theorem pc6Step37 : pc6Prefix36 * cMatrix = pc6Prefix37 := by decide +kernel
private def pc6Prefix38 : M := !![ofCode 0, ofCode 0, ofCode 0, ofCode 1; ofCode 0, ofCode 0, ofCode 1, ofCode 0; ofCode 0, ofCode 1, ofCode 0, ofCode 0; ofCode 1, ofCode 0, ofCode 0, ofCode 0]
private theorem pc6Step38 : pc6Prefix37 * bMatrix = pc6Prefix38 := by decide +kernel
private theorem pc6Step39 : pc6Prefix38 * cMatrix = pc6Matrix := by decide +kernel

theorem pc6_from_cb : b⁻¹ * c * b * c * b * b * c * b⁻¹ * c * b * c * b * b * c * b⁻¹ * c * b * c * b⁻¹ * c * b * b * c * b * c * b⁻¹ * c * b * c * b⁻¹ * c * b * c * b⁻¹ * c * b * b * c * b * c = pc6 := by
  apply Units.ext
  change bInverse * cMatrix * bMatrix * cMatrix * bMatrix * bMatrix * cMatrix * bInverse * cMatrix * bMatrix * cMatrix * bMatrix * bMatrix * cMatrix * bInverse * cMatrix * bMatrix * cMatrix * bInverse * cMatrix * bMatrix * bMatrix * cMatrix * bMatrix * cMatrix * bInverse * cMatrix * bMatrix * cMatrix * bInverse * cMatrix * bMatrix * cMatrix * bInverse * cMatrix * bMatrix * bMatrix * cMatrix * bMatrix * cMatrix = pc6Matrix
  rw [pc6Step1, pc6Step2, pc6Step3, pc6Step4, pc6Step5, pc6Step6, pc6Step7, pc6Step8, pc6Step9, pc6Step10, pc6Step11, pc6Step12, pc6Step13, pc6Step14, pc6Step15, pc6Step16, pc6Step17, pc6Step18, pc6Step19, pc6Step20, pc6Step21, pc6Step22, pc6Step23, pc6Step24, pc6Step25, pc6Step26, pc6Step27, pc6Step28, pc6Step29, pc6Step30, pc6Step31, pc6Step32, pc6Step33, pc6Step34, pc6Step35, pc6Step36, pc6Step37, pc6Step38, pc6Step39]

private def pc7Prefix1 : M := !![ofCode 6, ofCode 2, ofCode 3, ofCode 1; ofCode 0, ofCode 7, ofCode 1, ofCode 0; ofCode 3, ofCode 1, ofCode 0, ofCode 0; ofCode 1, ofCode 0, ofCode 0, ofCode 0]
private theorem pc7Step1 : bInverse * cMatrix = pc7Prefix1 := by decide +kernel
private def pc7Prefix2 : M := !![ofCode 6, ofCode 3, ofCode 6, ofCode 2; ofCode 0, ofCode 7, ofCode 2, ofCode 6; ofCode 3, ofCode 4, ofCode 7, ofCode 3; ofCode 1, ofCode 3, ofCode 0, ofCode 6]
private theorem pc7Step2 : pc7Prefix1 * bMatrix = pc7Prefix2 := by decide +kernel
private def pc7Prefix3 : M := !![ofCode 6, ofCode 2, ofCode 4, ofCode 7; ofCode 0, ofCode 7, ofCode 1, ofCode 5; ofCode 3, ofCode 1, ofCode 6, ofCode 3; ofCode 1, ofCode 0, ofCode 2, ofCode 6]
private theorem pc7Step3 : pc7Prefix2 * bMatrix = pc7Prefix3 := by decide +kernel
private def pc7Prefix4 : M := !![ofCode 7, ofCode 4, ofCode 2, ofCode 6; ofCode 5, ofCode 1, ofCode 7, ofCode 0; ofCode 3, ofCode 6, ofCode 1, ofCode 3; ofCode 6, ofCode 2, ofCode 0, ofCode 1]
private theorem pc7Step4 : pc7Prefix3 * cMatrix = pc7Prefix4 := by decide +kernel
private def pc7Prefix5 : M := !![ofCode 7, ofCode 6, ofCode 6, ofCode 4; ofCode 5, ofCode 5, ofCode 1, ofCode 1; ofCode 3, ofCode 3, ofCode 3, ofCode 1; ofCode 6, ofCode 3, ofCode 2, ofCode 3]
private theorem pc7Step5 : pc7Prefix4 * bInverse = pc7Prefix5 := by decide +kernel
private def pc7Prefix6 : M := !![ofCode 4, ofCode 6, ofCode 6, ofCode 7; ofCode 1, ofCode 1, ofCode 5, ofCode 5; ofCode 1, ofCode 3, ofCode 3, ofCode 3; ofCode 3, ofCode 2, ofCode 3, ofCode 6]
private theorem pc7Step6 : pc7Prefix5 * cMatrix = pc7Prefix6 := by decide +kernel
private def pc7Prefix7 : M := !![ofCode 4, ofCode 1, ofCode 2, ofCode 4; ofCode 1, ofCode 2, ofCode 2, ofCode 5; ofCode 1, ofCode 0, ofCode 1, ofCode 6; ofCode 3, ofCode 7, ofCode 6, ofCode 6]
private theorem pc7Step7 : pc7Prefix6 * bMatrix = pc7Prefix7 := by decide +kernel
private def pc7Prefix8 : M := !![ofCode 4, ofCode 2, ofCode 1, ofCode 4; ofCode 5, ofCode 2, ofCode 2, ofCode 1; ofCode 6, ofCode 1, ofCode 0, ofCode 1; ofCode 6, ofCode 6, ofCode 7, ofCode 3]
private theorem pc7Step8 : pc7Prefix7 * cMatrix = pc7Prefix8 := by decide +kernel
private def pc7Prefix9 : M := !![ofCode 4, ofCode 5, ofCode 7, ofCode 2; ofCode 5, ofCode 6, ofCode 6, ofCode 4; ofCode 6, ofCode 0, ofCode 0, ofCode 3; ofCode 6, ofCode 7, ofCode 4, ofCode 3]
private theorem pc7Step9 : pc7Prefix8 * bInverse = pc7Prefix9 := by decide +kernel
private def pc7Prefix10 : M := !![ofCode 2, ofCode 7, ofCode 5, ofCode 4; ofCode 4, ofCode 6, ofCode 6, ofCode 5; ofCode 3, ofCode 0, ofCode 0, ofCode 6; ofCode 3, ofCode 4, ofCode 7, ofCode 6]
private theorem pc7Step10 : pc7Prefix9 * cMatrix = pc7Prefix10 := by decide +kernel
private def pc7Prefix11 : M := !![ofCode 2, ofCode 1, ofCode 2, ofCode 7; ofCode 4, ofCode 1, ofCode 1, ofCode 1; ofCode 3, ofCode 5, ofCode 6, ofCode 7; ofCode 3, ofCode 1, ofCode 0, ofCode 5]
private theorem pc7Step11 : pc7Prefix10 * bInverse = pc7Prefix11 := by decide +kernel
private def pc7Prefix12 : M := !![ofCode 7, ofCode 2, ofCode 1, ofCode 2; ofCode 1, ofCode 1, ofCode 1, ofCode 4; ofCode 7, ofCode 6, ofCode 5, ofCode 3; ofCode 5, ofCode 0, ofCode 1, ofCode 3]
private theorem pc7Step12 : pc7Prefix11 * cMatrix = pc7Prefix12 := by decide +kernel
private def pc7Prefix13 : M := !![ofCode 7, ofCode 0, ofCode 4, ofCode 1; ofCode 1, ofCode 2, ofCode 6, ofCode 3; ofCode 7, ofCode 4, ofCode 1, ofCode 4; ofCode 5, ofCode 4, ofCode 1, ofCode 3]
private theorem pc7Step13 : pc7Prefix12 * bMatrix = pc7Prefix13 := by decide +kernel
private def pc7Prefix14 : M := !![ofCode 1, ofCode 4, ofCode 0, ofCode 7; ofCode 3, ofCode 6, ofCode 2, ofCode 1; ofCode 4, ofCode 1, ofCode 4, ofCode 7; ofCode 3, ofCode 1, ofCode 4, ofCode 5]
private theorem pc7Step14 : pc7Prefix13 * cMatrix = pc7Prefix14 := by decide +kernel
private def pc7Prefix15 : M := !![ofCode 1, ofCode 7, ofCode 1, ofCode 2; ofCode 3, ofCode 3, ofCode 6, ofCode 1; ofCode 4, ofCode 6, ofCode 3, ofCode 7; ofCode 3, ofCode 4, ofCode 3, ofCode 1]
private theorem pc7Step15 : pc7Prefix14 * bMatrix = pc7Prefix15 := by decide +kernel
private def pc7Prefix16 : M := !![ofCode 2, ofCode 1, ofCode 7, ofCode 1; ofCode 1, ofCode 6, ofCode 3, ofCode 3; ofCode 7, ofCode 3, ofCode 6, ofCode 4; ofCode 1, ofCode 3, ofCode 4, ofCode 3]
private theorem pc7Step16 : pc7Prefix15 * cMatrix = pc7Prefix16 := by decide +kernel
private def pc7Prefix17 : M := !![ofCode 2, ofCode 7, ofCode 4, ofCode 4; ofCode 1, ofCode 5, ofCode 5, ofCode 0; ofCode 7, ofCode 1, ofCode 1, ofCode 1; ofCode 1, ofCode 0, ofCode 4, ofCode 2]
private theorem pc7Step17 : pc7Prefix16 * bInverse = pc7Prefix17 := by decide +kernel
private def pc7Prefix18 : M := !![ofCode 4, ofCode 4, ofCode 7, ofCode 2; ofCode 0, ofCode 5, ofCode 5, ofCode 1; ofCode 1, ofCode 1, ofCode 1, ofCode 7; ofCode 2, ofCode 4, ofCode 0, ofCode 1]
private theorem pc7Step18 : pc7Prefix17 * cMatrix = pc7Prefix18 := by decide +kernel
private def pc7Prefix19 : M := !![ofCode 4, ofCode 3, ofCode 5, ofCode 5; ofCode 0, ofCode 5, ofCode 3, ofCode 5; ofCode 1, ofCode 2, ofCode 4, ofCode 2; ofCode 2, ofCode 2, ofCode 5, ofCode 6]
private theorem pc7Step19 : pc7Prefix18 * bInverse = pc7Prefix19 := by decide +kernel
private def pc7Prefix20 : M := !![ofCode 5, ofCode 5, ofCode 3, ofCode 4; ofCode 5, ofCode 3, ofCode 5, ofCode 0; ofCode 2, ofCode 4, ofCode 2, ofCode 1; ofCode 6, ofCode 5, ofCode 2, ofCode 2]
private theorem pc7Step20 : pc7Prefix19 * cMatrix = pc7Prefix20 := by decide +kernel
private def pc7Prefix21 : M := !![ofCode 5, ofCode 1, ofCode 5, ofCode 3; ofCode 5, ofCode 7, ofCode 7, ofCode 1; ofCode 2, ofCode 2, ofCode 3, ofCode 3; ofCode 6, ofCode 4, ofCode 4, ofCode 7]
private theorem pc7Step21 : pc7Prefix20 * bMatrix = pc7Prefix21 := by decide +kernel
private def pc7Prefix22 : M := !![ofCode 3, ofCode 5, ofCode 1, ofCode 5; ofCode 1, ofCode 7, ofCode 7, ofCode 5; ofCode 3, ofCode 3, ofCode 2, ofCode 2; ofCode 7, ofCode 4, ofCode 4, ofCode 6]
private theorem pc7Step22 : pc7Prefix21 * cMatrix = pc7Prefix22 := by decide +kernel
private def pc7Prefix23 : M := !![ofCode 3, ofCode 0, ofCode 1, ofCode 7; ofCode 1, ofCode 4, ofCode 6, ofCode 1; ofCode 3, ofCode 6, ofCode 6, ofCode 5; ofCode 7, ofCode 6, ofCode 0, ofCode 5]
private theorem pc7Step23 : pc7Prefix22 * bInverse = pc7Prefix23 := by decide +kernel
private def pc7Prefix24 : M := !![ofCode 7, ofCode 1, ofCode 0, ofCode 3; ofCode 1, ofCode 6, ofCode 4, ofCode 1; ofCode 5, ofCode 6, ofCode 6, ofCode 3; ofCode 5, ofCode 0, ofCode 6, ofCode 7]
private theorem pc7Step24 : pc7Prefix23 * cMatrix = pc7Prefix24 := by decide +kernel
private def pc7Prefix25 : M := !![ofCode 7, ofCode 3, ofCode 7, ofCode 5; ofCode 1, ofCode 5, ofCode 0, ofCode 7; ofCode 5, ofCode 2, ofCode 2, ofCode 6; ofCode 5, ofCode 4, ofCode 6, ofCode 5]
private theorem pc7Step25 : pc7Prefix24 * bMatrix = pc7Prefix25 := by decide +kernel
private def pc7Prefix26 : M := !![ofCode 5, ofCode 7, ofCode 3, ofCode 7; ofCode 7, ofCode 0, ofCode 5, ofCode 1; ofCode 6, ofCode 2, ofCode 2, ofCode 5; ofCode 5, ofCode 6, ofCode 4, ofCode 5]
private theorem pc7Step26 : pc7Prefix25 * cMatrix = pc7Prefix26 := by decide +kernel
private def pc7Prefix27 : M := !![ofCode 5, ofCode 3, ofCode 1, ofCode 1; ofCode 7, ofCode 2, ofCode 0, ofCode 1; ofCode 6, ofCode 3, ofCode 0, ofCode 1; ofCode 5, ofCode 2, ofCode 1, ofCode 1]
private theorem pc7Step27 : pc7Prefix26 * bInverse = pc7Prefix27 := by decide +kernel
private def pc7Prefix28 : M := !![ofCode 1, ofCode 1, ofCode 3, ofCode 5; ofCode 1, ofCode 0, ofCode 2, ofCode 7; ofCode 1, ofCode 0, ofCode 3, ofCode 6; ofCode 1, ofCode 1, ofCode 2, ofCode 5]
private theorem pc7Step28 : pc7Prefix27 * cMatrix = pc7Prefix28 := by decide +kernel
private def pc7Prefix29 : M := !![ofCode 1, ofCode 2, ofCode 4, ofCode 4; ofCode 1, ofCode 3, ofCode 2, ofCode 7; ofCode 1, ofCode 3, ofCode 3, ofCode 5; ofCode 1, ofCode 2, ofCode 5, ofCode 7]
private theorem pc7Step29 : pc7Prefix28 * bMatrix = pc7Prefix29 := by decide +kernel
private def pc7Prefix30 : M := !![ofCode 4, ofCode 4, ofCode 2, ofCode 1; ofCode 7, ofCode 2, ofCode 3, ofCode 1; ofCode 5, ofCode 3, ofCode 3, ofCode 1; ofCode 7, ofCode 5, ofCode 2, ofCode 1]
private theorem pc7Step30 : pc7Prefix29 * cMatrix = pc7Prefix30 := by decide +kernel
private def pc7Prefix31 : M := !![ofCode 4, ofCode 3, ofCode 0, ofCode 2; ofCode 7, ofCode 0, ofCode 3, ofCode 0; ofCode 5, ofCode 7, ofCode 0, ofCode 7; ofCode 7, ofCode 7, ofCode 1, ofCode 3]
private theorem pc7Step31 : pc7Prefix30 * bInverse = pc7Prefix31 := by decide +kernel
private def pc7Prefix32 : M := !![ofCode 2, ofCode 0, ofCode 3, ofCode 4; ofCode 0, ofCode 3, ofCode 0, ofCode 7; ofCode 7, ofCode 0, ofCode 7, ofCode 5; ofCode 3, ofCode 1, ofCode 7, ofCode 7]
private theorem pc7Step32 : pc7Prefix31 * cMatrix = pc7Prefix32 := by decide +kernel
private def pc7Prefix33 : M := !![ofCode 2, ofCode 6, ofCode 3, ofCode 6; ofCode 0, ofCode 3, ofCode 2, ofCode 1; ofCode 7, ofCode 2, ofCode 7, ofCode 3; ofCode 3, ofCode 4, ofCode 0, ofCode 6]
private theorem pc7Step33 : pc7Prefix32 * bMatrix = pc7Prefix33 := by decide +kernel
private def pc7Prefix34 : M := !![ofCode 6, ofCode 3, ofCode 6, ofCode 2; ofCode 1, ofCode 2, ofCode 3, ofCode 0; ofCode 3, ofCode 7, ofCode 2, ofCode 7; ofCode 6, ofCode 0, ofCode 4, ofCode 3]
private theorem pc7Step34 : pc7Prefix33 * cMatrix = pc7Prefix34 := by decide +kernel
private def pc7Prefix35 : M := !![ofCode 6, ofCode 2, ofCode 3, ofCode 1; ofCode 1, ofCode 1, ofCode 4, ofCode 3; ofCode 3, ofCode 2, ofCode 7, ofCode 0; ofCode 6, ofCode 1, ofCode 3, ofCode 6]
private theorem pc7Step35 : pc7Prefix34 * bInverse = pc7Prefix35 := by decide +kernel
private def pc7Prefix36 : M := !![ofCode 1, ofCode 3, ofCode 2, ofCode 6; ofCode 3, ofCode 4, ofCode 1, ofCode 1; ofCode 0, ofCode 7, ofCode 2, ofCode 3; ofCode 6, ofCode 3, ofCode 1, ofCode 6]
private theorem pc7Step36 : pc7Prefix35 * cMatrix = pc7Prefix36 := by decide +kernel
private def pc7Prefix37 : M := !![ofCode 1, ofCode 0, ofCode 0, ofCode 0; ofCode 3, ofCode 1, ofCode 0, ofCode 0; ofCode 0, ofCode 7, ofCode 1, ofCode 0; ofCode 6, ofCode 2, ofCode 3, ofCode 1]
private theorem pc7Step37 : pc7Prefix36 * bMatrix = pc7Prefix37 := by decide +kernel
private def pc7Prefix38 : M := !![ofCode 0, ofCode 0, ofCode 0, ofCode 1; ofCode 0, ofCode 0, ofCode 1, ofCode 3; ofCode 0, ofCode 1, ofCode 7, ofCode 0; ofCode 1, ofCode 3, ofCode 2, ofCode 6]
private theorem pc7Step38 : pc7Prefix37 * cMatrix = pc7Prefix38 := by decide +kernel
private def pc7Prefix39 : M := !![ofCode 0, ofCode 0, ofCode 0, ofCode 1; ofCode 0, ofCode 0, ofCode 1, ofCode 0; ofCode 0, ofCode 1, ofCode 0, ofCode 0; ofCode 1, ofCode 0, ofCode 0, ofCode 0]
private theorem pc7Step39 : pc7Prefix38 * bMatrix = pc7Prefix39 := by decide +kernel
private theorem pc7Step40 : pc7Prefix39 * cMatrix = pc7Matrix := by decide +kernel

theorem pc7_from_cb : b⁻¹ * c * b * b * c * b⁻¹ * c * b * c * b⁻¹ * c * b⁻¹ * c * b * c * b * c * b⁻¹ * c * b⁻¹ * c * b * c * b⁻¹ * c * b * c * b⁻¹ * c * b * c * b⁻¹ * c * b * c * b⁻¹ * c * b * c * b * c = pc7 := by
  apply Units.ext
  change bInverse * cMatrix * bMatrix * bMatrix * cMatrix * bInverse * cMatrix * bMatrix * cMatrix * bInverse * cMatrix * bInverse * cMatrix * bMatrix * cMatrix * bMatrix * cMatrix * bInverse * cMatrix * bInverse * cMatrix * bMatrix * cMatrix * bInverse * cMatrix * bMatrix * cMatrix * bInverse * cMatrix * bMatrix * cMatrix * bInverse * cMatrix * bMatrix * cMatrix * bInverse * cMatrix * bMatrix * cMatrix * bMatrix * cMatrix = pc7Matrix
  rw [pc7Step1, pc7Step2, pc7Step3, pc7Step4, pc7Step5, pc7Step6, pc7Step7, pc7Step8, pc7Step9, pc7Step10, pc7Step11, pc7Step12, pc7Step13, pc7Step14, pc7Step15, pc7Step16, pc7Step17, pc7Step18, pc7Step19, pc7Step20, pc7Step21, pc7Step22, pc7Step23, pc7Step24, pc7Step25, pc7Step26, pc7Step27, pc7Step28, pc7Step29, pc7Step30, pc7Step31, pc7Step32, pc7Step33, pc7Step34, pc7Step35, pc7Step36, pc7Step37, pc7Step38, pc7Step39, pc7Step40]

private def torusPrefix1 : M := !![ofCode 0, ofCode 0, ofCode 0, ofCode 1; ofCode 0, ofCode 0, ofCode 1, ofCode 3; ofCode 0, ofCode 1, ofCode 7, ofCode 2; ofCode 1, ofCode 3, ofCode 0, ofCode 6]
private theorem torusStep1 : cMatrix * bMatrix = torusPrefix1 := by decide +kernel
private def torusPrefix2 : M := !![ofCode 1, ofCode 0, ofCode 0, ofCode 0; ofCode 3, ofCode 1, ofCode 0, ofCode 0; ofCode 2, ofCode 7, ofCode 1, ofCode 0; ofCode 6, ofCode 0, ofCode 3, ofCode 1]
private theorem torusStep2 : torusPrefix1 * cMatrix = torusPrefix2 := by decide +kernel
private def torusPrefix3 : M := !![ofCode 1, ofCode 3, ofCode 2, ofCode 6; ofCode 3, ofCode 4, ofCode 1, ofCode 1; ofCode 2, ofCode 1, ofCode 6, ofCode 4; ofCode 6, ofCode 1, ofCode 4, ofCode 6]
private theorem torusStep3 : torusPrefix2 * bInverse = torusPrefix3 := by decide +kernel
private def torusPrefix4 : M := !![ofCode 6, ofCode 2, ofCode 3, ofCode 1; ofCode 1, ofCode 1, ofCode 4, ofCode 3; ofCode 4, ofCode 6, ofCode 1, ofCode 2; ofCode 6, ofCode 4, ofCode 1, ofCode 6]
private theorem torusStep4 : torusPrefix3 * cMatrix = torusPrefix4 := by decide +kernel
private def torusPrefix5 : M := !![ofCode 6, ofCode 3, ofCode 1, ofCode 6; ofCode 1, ofCode 2, ofCode 1, ofCode 2; ofCode 4, ofCode 1, ofCode 6, ofCode 4; ofCode 6, ofCode 5, ofCode 7, ofCode 7]
private theorem torusStep5 : torusPrefix4 * bInverse = torusPrefix5 := by decide +kernel
private def torusPrefix6 : M := !![ofCode 6, ofCode 1, ofCode 3, ofCode 6; ofCode 2, ofCode 1, ofCode 2, ofCode 1; ofCode 4, ofCode 6, ofCode 1, ofCode 4; ofCode 7, ofCode 7, ofCode 5, ofCode 6]
private theorem torusStep6 : torusPrefix5 * cMatrix = torusPrefix6 := by decide +kernel
private def torusPrefix7 : M := !![ofCode 6, ofCode 0, ofCode 4, ofCode 3; ofCode 2, ofCode 7, ofCode 5, ofCode 2; ofCode 4, ofCode 1, ofCode 5, ofCode 5; ofCode 7, ofCode 5, ofCode 6, ofCode 3]
private theorem torusStep7 : torusPrefix6 * bMatrix = torusPrefix7 := by decide +kernel
private def torusPrefix8 : M := !![ofCode 3, ofCode 4, ofCode 0, ofCode 6; ofCode 2, ofCode 5, ofCode 7, ofCode 2; ofCode 5, ofCode 5, ofCode 1, ofCode 4; ofCode 3, ofCode 6, ofCode 5, ofCode 7]
private theorem torusStep8 : torusPrefix7 * cMatrix = torusPrefix8 := by decide +kernel
private def torusPrefix9 : M := !![ofCode 3, ofCode 1, ofCode 7, ofCode 7; ofCode 2, ofCode 3, ofCode 5, ofCode 7; ofCode 5, ofCode 1, ofCode 6, ofCode 4; ofCode 3, ofCode 3, ofCode 7, ofCode 2]
private theorem torusStep9 : torusPrefix8 * bInverse = torusPrefix9 := by decide +kernel
private def torusPrefix10 : M := !![ofCode 7, ofCode 7, ofCode 1, ofCode 3; ofCode 7, ofCode 5, ofCode 3, ofCode 2; ofCode 4, ofCode 6, ofCode 1, ofCode 5; ofCode 2, ofCode 7, ofCode 3, ofCode 3]
private theorem torusStep10 : torusPrefix9 * cMatrix = torusPrefix10 := by decide +kernel
private def torusPrefix11 : M := !![ofCode 7, ofCode 5, ofCode 2, ofCode 1; ofCode 7, ofCode 7, ofCode 5, ofCode 2; ofCode 4, ofCode 1, ofCode 5, ofCode 4; ofCode 2, ofCode 1, ofCode 0, ofCode 4]
private theorem torusStep11 : torusPrefix10 * bMatrix = torusPrefix11 := by decide +kernel
private def torusPrefix12 : M := !![ofCode 1, ofCode 2, ofCode 5, ofCode 7; ofCode 2, ofCode 5, ofCode 7, ofCode 7; ofCode 4, ofCode 5, ofCode 1, ofCode 4; ofCode 4, ofCode 0, ofCode 1, ofCode 2]
private theorem torusStep12 : torusPrefix11 * cMatrix = torusPrefix12 := by decide +kernel
private def torusPrefix13 : M := !![ofCode 1, ofCode 1, ofCode 0, ofCode 1; ofCode 2, ofCode 3, ofCode 1, ofCode 3; ofCode 4, ofCode 2, ofCode 7, ofCode 3; ofCode 4, ofCode 7, ofCode 1, ofCode 4]
private theorem torusStep13 : torusPrefix12 * bMatrix = torusPrefix13 := by decide +kernel
private def torusPrefix14 : M := !![ofCode 1, ofCode 2, ofCode 7, ofCode 5; ofCode 2, ofCode 5, ofCode 3, ofCode 1; ofCode 4, ofCode 5, ofCode 2, ofCode 0; ofCode 4, ofCode 0, ofCode 2, ofCode 7]
private theorem torusStep14 : torusPrefix13 * bMatrix = torusPrefix14 := by decide +kernel
private def torusPrefix15 : M := !![ofCode 5, ofCode 7, ofCode 2, ofCode 1; ofCode 1, ofCode 3, ofCode 5, ofCode 2; ofCode 0, ofCode 2, ofCode 5, ofCode 4; ofCode 7, ofCode 2, ofCode 0, ofCode 4]
private theorem torusStep15 : torusPrefix14 * cMatrix = torusPrefix15 := by decide +kernel
private def torusPrefix16 : M := !![ofCode 5, ofCode 3, ofCode 0, ofCode 4; ofCode 1, ofCode 0, ofCode 5, ofCode 0; ofCode 0, ofCode 2, ofCode 0, ofCode 0; ofCode 7, ofCode 0, ofCode 0, ofCode 0]
private theorem torusStep16 : torusPrefix15 * bInverse = torusPrefix16 := by decide +kernel
private def torusPrefix17 : M := !![ofCode 4, ofCode 0, ofCode 3, ofCode 5; ofCode 0, ofCode 5, ofCode 0, ofCode 1; ofCode 0, ofCode 0, ofCode 2, ofCode 0; ofCode 0, ofCode 0, ofCode 0, ofCode 7]
private theorem torusStep17 : torusPrefix16 * cMatrix = torusPrefix17 := by decide +kernel
private def torusPrefix18 : M := !![ofCode 4, ofCode 7, ofCode 3, ofCode 5; ofCode 0, ofCode 5, ofCode 6, ofCode 0; ofCode 0, ofCode 0, ofCode 2, ofCode 6; ofCode 0, ofCode 0, ofCode 0, ofCode 7]
private theorem torusStep18 : torusPrefix17 * bMatrix = torusPrefix18 := by decide +kernel
private theorem torusStep19 : torusPrefix18 * bMatrix = torusMatrix := by decide +kernel

theorem torus_from_cb : c * b * c * b⁻¹ * c * b⁻¹ * c * b * c * b⁻¹ * c * b * c * b * b * c * b⁻¹ * c * b * b = torus := by
  apply Units.ext
  change cMatrix * bMatrix * cMatrix * bInverse * cMatrix * bInverse * cMatrix * bMatrix * cMatrix * bInverse * cMatrix * bMatrix * cMatrix * bMatrix * bMatrix * cMatrix * bInverse * cMatrix * bMatrix * bMatrix = torusMatrix
  rw [torusStep1, torusStep2, torusStep3, torusStep4, torusStep5, torusStep6, torusStep7, torusStep8, torusStep9, torusStep10, torusStep11, torusStep12, torusStep13, torusStep14, torusStep15, torusStep16, torusStep17, torusStep18, torusStep19]

end Kourovka2135.SuzukiEightCoverCodeMatrices
