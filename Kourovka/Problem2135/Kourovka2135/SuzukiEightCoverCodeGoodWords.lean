import Kourovka2135.SuzukiEightCoverSemilinear

/-! Exact canonical good-pair words, including the outer automorphism. -/
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
namespace Kourovka2135.SuzukiEightCoverCodeGoodWords
open SuzukiEightCodeField SuzukiEightCoverCodeMatrices
open SuzukiEightCoverSemilinear (outerAut)

def xMatrix : M := !![ofCode 1, ofCode 0, ofCode 2, ofCode 6; ofCode 0, ofCode 1, ofCode 0, ofCode 2; ofCode 2, ofCode 0, ofCode 5, ofCode 7; ofCode 6, ofCode 2, ofCode 7, ofCode 7]
def xInverse : M := !![ofCode 7, ofCode 7, ofCode 2, ofCode 6; ofCode 7, ofCode 5, ofCode 0, ofCode 2; ofCode 2, ofCode 0, ofCode 1, ofCode 0; ofCode 6, ofCode 2, ofCode 0, ofCode 1]
theorem x_mul_inverse : xMatrix * xInverse = 1 := by decide +kernel
theorem x_inverse_mul : xInverse * xMatrix = 1 := by decide +kernel
def x : UnitMatrix := ⟨xMatrix, xInverse, x_mul_inverse, x_inverse_mul⟩

def zMatrix : M := !![ofCode 1, ofCode 1, ofCode 5, ofCode 7; ofCode 7, ofCode 6, ofCode 7, ofCode 7; ofCode 4, ofCode 1, ofCode 6, ofCode 2; ofCode 7, ofCode 5, ofCode 3, ofCode 6]
def zInverse : M := !![ofCode 6, ofCode 2, ofCode 7, ofCode 7; ofCode 3, ofCode 6, ofCode 7, ofCode 5; ofCode 5, ofCode 1, ofCode 6, ofCode 1; ofCode 7, ofCode 4, ofCode 7, ofCode 1]
theorem z_mul_inverse : zMatrix * zInverse = 1 := by decide +kernel
theorem z_inverse_mul : zInverse * zMatrix = 1 := by decide +kernel
def z : UnitMatrix := ⟨zMatrix, zInverse, z_mul_inverse, z_inverse_mul⟩

def yMatrix : M := !![ofCode 3, ofCode 2, ofCode 3, ofCode 6; ofCode 1, ofCode 3, ofCode 3, ofCode 3; ofCode 1, ofCode 1, ofCode 5, ofCode 5; ofCode 4, ofCode 6, ofCode 6, ofCode 7]
def yInverse : M := !![ofCode 7, ofCode 5, ofCode 3, ofCode 6; ofCode 6, ofCode 5, ofCode 3, ofCode 3; ofCode 6, ofCode 1, ofCode 3, ofCode 2; ofCode 4, ofCode 1, ofCode 1, ofCode 3]
theorem y_mul_inverse : yMatrix * yInverse = 1 := by decide +kernel
theorem y_inverse_mul : yInverse * yMatrix = 1 := by decide +kernel
def y : UnitMatrix := ⟨yMatrix, yInverse, y_mul_inverse, y_inverse_mul⟩

def kMatrix : M := !![ofCode 5, ofCode 1, ofCode 2, ofCode 2; ofCode 1, ofCode 4, ofCode 6, ofCode 5; ofCode 1, ofCode 0, ofCode 0, ofCode 4; ofCode 6, ofCode 4, ofCode 2, ofCode 5]
def kInverse : M := !![ofCode 5, ofCode 4, ofCode 5, ofCode 2; ofCode 2, ofCode 0, ofCode 6, ofCode 2; ofCode 4, ofCode 0, ofCode 4, ofCode 1; ofCode 6, ofCode 1, ofCode 1, ofCode 5]
theorem k_mul_inverse : kMatrix * kInverse = 1 := by decide +kernel
theorem k_inverse_mul : kInverse * kMatrix = 1 := by decide +kernel
def k : UnitMatrix := ⟨kMatrix, kInverse, k_mul_inverse, k_inverse_mul⟩

def adMatrix : M := !![ofCode 2, ofCode 0, ofCode 1, ofCode 6; ofCode 3, ofCode 3, ofCode 4, ofCode 1; ofCode 1, ofCode 6, ofCode 3, ofCode 0; ofCode 7, ofCode 1, ofCode 3, ofCode 2]
def adInverse : M := !![ofCode 2, ofCode 0, ofCode 1, ofCode 6; ofCode 3, ofCode 3, ofCode 4, ofCode 1; ofCode 1, ofCode 6, ofCode 3, ofCode 0; ofCode 7, ofCode 1, ofCode 3, ofCode 2]
theorem ad_mul_inverse : adMatrix * adInverse = 1 := by decide +kernel
theorem ad_inverse_mul : adInverse * adMatrix = 1 := by decide +kernel
def ad : UnitMatrix := ⟨adMatrix, adInverse, ad_mul_inverse, ad_inverse_mul⟩

def bdMatrix : M := !![ofCode 6, ofCode 0, ofCode 7, ofCode 2; ofCode 1, ofCode 7, ofCode 2, ofCode 3; ofCode 0, ofCode 3, ofCode 4, ofCode 6; ofCode 2, ofCode 5, ofCode 3, ofCode 5]
def bdInverse : M := !![ofCode 5, ofCode 6, ofCode 3, ofCode 2; ofCode 3, ofCode 4, ofCode 2, ofCode 7; ofCode 5, ofCode 3, ofCode 7, ofCode 0; ofCode 2, ofCode 0, ofCode 1, ofCode 6]
theorem bd_mul_inverse : bdMatrix * bdInverse = 1 := by decide +kernel
theorem bd_inverse_mul : bdInverse * bdMatrix = 1 := by decide +kernel
def bd : UnitMatrix := ⟨bdMatrix, bdInverse, bd_mul_inverse, bd_inverse_mul⟩

private def x_from_cbPrefix1 : M := !![ofCode 0, ofCode 0, ofCode 0, ofCode 1; ofCode 0, ofCode 0, ofCode 1, ofCode 3; ofCode 0, ofCode 1, ofCode 7, ofCode 2; ofCode 1, ofCode 3, ofCode 0, ofCode 6]
private theorem x_from_cbStep1 : cMatrix * bMatrix = x_from_cbPrefix1 := by decide +kernel
private def x_from_cbPrefix2 : M := !![ofCode 0, ofCode 0, ofCode 0, ofCode 1; ofCode 0, ofCode 0, ofCode 1, ofCode 0; ofCode 0, ofCode 1, ofCode 0, ofCode 2; ofCode 1, ofCode 0, ofCode 2, ofCode 6]
private theorem x_from_cbStep2 : x_from_cbPrefix1 * bMatrix = x_from_cbPrefix2 := by decide +kernel
private def x_from_cbPrefix3 : M := !![ofCode 1, ofCode 0, ofCode 0, ofCode 0; ofCode 0, ofCode 1, ofCode 0, ofCode 0; ofCode 2, ofCode 0, ofCode 1, ofCode 0; ofCode 6, ofCode 2, ofCode 0, ofCode 1]
private theorem x_from_cbStep3 : x_from_cbPrefix2 * cMatrix = x_from_cbPrefix3 := by decide +kernel
private def x_from_cbPrefix4 : M := !![ofCode 1, ofCode 3, ofCode 0, ofCode 6; ofCode 0, ofCode 1, ofCode 7, ofCode 2; ofCode 2, ofCode 6, ofCode 1, ofCode 4; ofCode 6, ofCode 3, ofCode 5, ofCode 7]
private theorem x_from_cbStep4 : x_from_cbPrefix3 * bMatrix = x_from_cbPrefix4 := by decide +kernel
private theorem x_from_cbStep5 : x_from_cbPrefix4 * bMatrix = xMatrix := by decide +kernel
theorem x_from_cb : c * b * b * c * b * b = x := by
  apply Units.ext
  change cMatrix * bMatrix * bMatrix * cMatrix * bMatrix * bMatrix = xMatrix
  rw [x_from_cbStep1, x_from_cbStep2, x_from_cbStep3, x_from_cbStep4, x_from_cbStep5]

private def z_from_cbPrefix1 : M := !![ofCode 1, ofCode 0, ofCode 2, ofCode 6; ofCode 0, ofCode 1, ofCode 0, ofCode 2; ofCode 0, ofCode 0, ofCode 1, ofCode 0; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem z_from_cbStep1 : bMatrix * bMatrix = z_from_cbPrefix1 := by decide +kernel
private def z_from_cbPrefix2 : M := !![ofCode 6, ofCode 2, ofCode 0, ofCode 1; ofCode 2, ofCode 0, ofCode 1, ofCode 0; ofCode 0, ofCode 1, ofCode 0, ofCode 0; ofCode 1, ofCode 0, ofCode 0, ofCode 0]
private theorem z_from_cbStep2 : z_from_cbPrefix1 * cMatrix = z_from_cbPrefix2 := by decide +kernel
private def z_from_cbPrefix3 : M := !![ofCode 6, ofCode 3, ofCode 5, ofCode 7; ofCode 2, ofCode 6, ofCode 1, ofCode 4; ofCode 0, ofCode 1, ofCode 7, ofCode 2; ofCode 1, ofCode 3, ofCode 0, ofCode 6]
private theorem z_from_cbStep3 : z_from_cbPrefix2 * bMatrix = z_from_cbPrefix3 := by decide +kernel
private def z_from_cbPrefix4 : M := !![ofCode 6, ofCode 2, ofCode 7, ofCode 7; ofCode 2, ofCode 0, ofCode 5, ofCode 7; ofCode 0, ofCode 1, ofCode 0, ofCode 2; ofCode 1, ofCode 0, ofCode 2, ofCode 6]
private theorem z_from_cbStep4 : z_from_cbPrefix3 * bMatrix = z_from_cbPrefix4 := by decide +kernel
private def z_from_cbPrefix5 : M := !![ofCode 7, ofCode 7, ofCode 2, ofCode 6; ofCode 7, ofCode 5, ofCode 0, ofCode 2; ofCode 2, ofCode 0, ofCode 1, ofCode 0; ofCode 6, ofCode 2, ofCode 0, ofCode 1]
private theorem z_from_cbStep5 : z_from_cbPrefix4 * cMatrix = z_from_cbPrefix5 := by decide +kernel
private def z_from_cbPrefix6 : M := !![ofCode 7, ofCode 5, ofCode 1, ofCode 1; ofCode 7, ofCode 7, ofCode 6, ofCode 7; ofCode 2, ofCode 6, ofCode 1, ofCode 4; ofCode 6, ofCode 3, ofCode 5, ofCode 7]
private theorem z_from_cbStep6 : z_from_cbPrefix5 * bMatrix = z_from_cbPrefix6 := by decide +kernel
private theorem z_from_cbStep7 : z_from_cbPrefix6 * cMatrix = zMatrix := by decide +kernel
theorem z_from_cb : b * b * c * b * b * c * b * c = z := by
  apply Units.ext
  change bMatrix * bMatrix * cMatrix * bMatrix * bMatrix * cMatrix * bMatrix * cMatrix = zMatrix
  rw [z_from_cbStep1, z_from_cbStep2, z_from_cbStep3, z_from_cbStep4, z_from_cbStep5, z_from_cbStep6, z_from_cbStep7]

private def y_conjugatePrefix1 : M := !![ofCode 7, ofCode 7, ofCode 2, ofCode 6; ofCode 5, ofCode 7, ofCode 6, ofCode 3; ofCode 4, ofCode 3, ofCode 5, ofCode 2; ofCode 4, ofCode 6, ofCode 4, ofCode 3]
private theorem y_conjugateStep1 : zInverse * xMatrix = y_conjugatePrefix1 := by decide +kernel
private theorem y_conjugateStep2 : y_conjugatePrefix1 * zMatrix = yMatrix := by decide +kernel
theorem y_conjugate : z⁻¹ * x * z = y := by
  apply Units.ext
  change zInverse * xMatrix * zMatrix = yMatrix
  rw [y_conjugateStep1, y_conjugateStep2]

private def commutatorPrefix1 : M := !![ofCode 5, ofCode 4, ofCode 0, ofCode 3; ofCode 3, ofCode 3, ofCode 4, ofCode 6; ofCode 3, ofCode 0, ofCode 5, ofCode 5; ofCode 7, ofCode 3, ofCode 6, ofCode 7]
private theorem commutatorStep1 : xInverse * yInverse = commutatorPrefix1 := by decide +kernel
private def commutatorPrefix2 : M := !![ofCode 4, ofCode 2, ofCode 3, ofCode 2; ofCode 2, ofCode 4, ofCode 0, ofCode 2; ofCode 1, ofCode 1, ofCode 7, ofCode 1; ofCode 4, ofCode 6, ofCode 5, ofCode 5]
private theorem commutatorStep2 : commutatorPrefix1 * xMatrix = commutatorPrefix2 := by decide +kernel
private theorem commutatorStep3 : commutatorPrefix2 * yMatrix = kMatrix := by decide +kernel
theorem commutator : x⁻¹ * y⁻¹ * x * y = k := by
  apply Units.ext
  change xInverse * yInverse * xMatrix * yMatrix = kMatrix
  rw [commutatorStep1, commutatorStep2, commutatorStep3]

private def c_from_xyPrefix1 : M := !![ofCode 7, ofCode 5, ofCode 6, ofCode 3; ofCode 6, ofCode 5, ofCode 4, ofCode 0; ofCode 3, ofCode 0, ofCode 3, ofCode 4; ofCode 7, ofCode 3, ofCode 3, ofCode 5]
private theorem c_from_xyStep1 : yMatrix * xMatrix = c_from_xyPrefix1 := by decide +kernel
private def c_from_xyPrefix2 : M := !![ofCode 6, ofCode 6, ofCode 4, ofCode 1; ofCode 0, ofCode 7, ofCode 7, ofCode 4; ofCode 0, ofCode 0, ofCode 4, ofCode 4; ofCode 0, ofCode 0, ofCode 0, ofCode 3]
private theorem c_from_xyStep2 : c_from_xyPrefix1 * yMatrix = c_from_xyPrefix2 := by decide +kernel
private def c_from_xyPrefix3 : M := !![ofCode 7, ofCode 4, ofCode 4, ofCode 6; ofCode 6, ofCode 0, ofCode 1, ofCode 5; ofCode 2, ofCode 1, ofCode 7, ofCode 3; ofCode 7, ofCode 1, ofCode 1, ofCode 2]
private theorem c_from_xyStep3 : c_from_xyPrefix2 * yMatrix = c_from_xyPrefix3 := by decide +kernel
private def c_from_xyPrefix4 : M := !![ofCode 6, ofCode 3, ofCode 3, ofCode 2; ofCode 7, ofCode 1, ofCode 4, ofCode 3; ofCode 6, ofCode 7, ofCode 0, ofCode 4; ofCode 2, ofCode 5, ofCode 5, ofCode 4]
private theorem c_from_xyStep4 : c_from_xyPrefix3 * xMatrix = c_from_xyPrefix4 := by decide +kernel
private def c_from_xyPrefix5 : M := !![ofCode 7, ofCode 7, ofCode 6, ofCode 3; ofCode 5, ofCode 7, ofCode 5, ofCode 5; ofCode 3, ofCode 4, ofCode 6, ofCode 6; ofCode 6, ofCode 6, ofCode 2, ofCode 1]
private theorem c_from_xyStep5 : c_from_xyPrefix4 * xMatrix = c_from_xyPrefix5 := by decide +kernel
private def c_from_xyPrefix6 : M := !![ofCode 2, ofCode 5, ofCode 2, ofCode 4; ofCode 3, ofCode 1, ofCode 7, ofCode 4; ofCode 0, ofCode 6, ofCode 5, ofCode 0; ofCode 5, ofCode 3, ofCode 7, ofCode 4]
private theorem c_from_xyStep6 : c_from_xyPrefix5 * yInverse = c_from_xyPrefix6 := by decide +kernel
private def c_from_xyPrefix7 : M := !![ofCode 2, ofCode 1, ofCode 6, ofCode 2; ofCode 5, ofCode 4, ofCode 1, ofCode 7; ofCode 5, ofCode 3, ofCode 5, ofCode 7; ofCode 4, ofCode 1, ofCode 6, ofCode 1]
private theorem c_from_xyStep7 : c_from_xyPrefix6 * xInverse = c_from_xyPrefix7 := by decide +kernel
private def c_from_xyPrefix8 : M := !![ofCode 2, ofCode 0, ofCode 6, ofCode 5; ofCode 4, ofCode 3, ofCode 7, ofCode 4; ofCode 5, ofCode 1, ofCode 2, ofCode 5; ofCode 1, ofCode 0, ofCode 4, ofCode 2]
private theorem c_from_xyStep8 : c_from_xyPrefix7 * yInverse = c_from_xyPrefix8 := by decide +kernel
private def c_from_xyPrefix9 : M := !![ofCode 5, ofCode 2, ofCode 2, ofCode 4; ofCode 2, ofCode 5, ofCode 4, ofCode 2; ofCode 5, ofCode 5, ofCode 4, ofCode 0; ofCode 1, ofCode 3, ofCode 6, ofCode 3]
private theorem c_from_xyStep9 : c_from_xyPrefix8 * yInverse = c_from_xyPrefix9 := by decide +kernel
private def c_from_xyPrefix10 : M := !![ofCode 4, ofCode 1, ofCode 1, ofCode 3; ofCode 6, ofCode 1, ofCode 3, ofCode 2; ofCode 6, ofCode 5, ofCode 3, ofCode 3; ofCode 7, ofCode 5, ofCode 3, ofCode 6]
private theorem c_from_xyStep10 : c_from_xyPrefix9 * xMatrix = c_from_xyPrefix10 := by decide +kernel
private theorem c_from_xyStep11 : c_from_xyPrefix10 * yMatrix = cMatrix := by decide +kernel
theorem c_from_xy : y * x * y * y * x * x * y⁻¹ * x⁻¹ * y⁻¹ * y⁻¹ * x * y = c := by
  apply Units.ext
  change yMatrix * xMatrix * yMatrix * yMatrix * xMatrix * xMatrix * yInverse * xInverse * yInverse * yInverse * xMatrix * yMatrix = cMatrix
  rw [c_from_xyStep1, c_from_xyStep2, c_from_xyStep3, c_from_xyStep4, c_from_xyStep5, c_from_xyStep6, c_from_xyStep7, c_from_xyStep8, c_from_xyStep9, c_from_xyStep10, c_from_xyStep11]

private def b_from_xyPrefix1 : M := !![ofCode 7, ofCode 7, ofCode 7, ofCode 7; ofCode 7, ofCode 5, ofCode 5, ofCode 7; ofCode 7, ofCode 5, ofCode 0, ofCode 2; ofCode 7, ofCode 7, ofCode 2, ofCode 6]
private theorem b_from_xyStep1 : xMatrix * xMatrix = b_from_xyPrefix1 := by decide +kernel
private def b_from_xyPrefix2 : M := !![ofCode 2, ofCode 0, ofCode 5, ofCode 1; ofCode 2, ofCode 3, ofCode 5, ofCode 3; ofCode 3, ofCode 3, ofCode 4, ofCode 6; ofCode 5, ofCode 4, ofCode 0, ofCode 3]
private theorem b_from_xyStep2 : b_from_xyPrefix1 * yInverse = b_from_xyPrefix2 := by decide +kernel
private def b_from_xyPrefix3 : M := !![ofCode 5, ofCode 2, ofCode 4, ofCode 6; ofCode 2, ofCode 5, ofCode 1, ofCode 5; ofCode 2, ofCode 4, ofCode 0, ofCode 2; ofCode 4, ofCode 2, ofCode 3, ofCode 2]
private theorem b_from_xyStep3 : b_from_xyPrefix2 * xMatrix = b_from_xyPrefix3 := by decide +kernel
private def b_from_xyPrefix4 : M := !![ofCode 7, ofCode 1, ofCode 2, ofCode 3; ofCode 0, ofCode 2, ofCode 4, ofCode 0; ofCode 1, ofCode 4, ofCode 6, ofCode 5; ofCode 5, ofCode 1, ofCode 2, ofCode 2]
private theorem b_from_xyStep4 : b_from_xyPrefix3 * yMatrix = b_from_xyPrefix4 := by decide +kernel
private def b_from_xyPrefix5 : M := !![ofCode 1, ofCode 0, ofCode 7, ofCode 5; ofCode 6, ofCode 1, ofCode 4, ofCode 4; ofCode 2, ofCode 4, ofCode 4, ofCode 0; ofCode 2, ofCode 7, ofCode 3, ofCode 3]
private theorem b_from_xyStep5 : b_from_xyPrefix4 * xInverse = b_from_xyPrefix5 := by decide +kernel
private def b_from_xyPrefix6 : M := !![ofCode 1, ofCode 7, ofCode 4, ofCode 7; ofCode 1, ofCode 6, ofCode 1, ofCode 5; ofCode 5, ofCode 7, ofCode 6, ofCode 3; ofCode 7, ofCode 7, ofCode 2, ofCode 6]
private theorem b_from_xyStep6 : b_from_xyPrefix5 * yInverse = b_from_xyPrefix6 := by decide +kernel
private def b_from_xyPrefix7 : M := !![ofCode 3, ofCode 4, ofCode 6, ofCode 4; ofCode 2, ofCode 5, ofCode 3, ofCode 4; ofCode 3, ofCode 6, ofCode 7, ofCode 5; ofCode 6, ofCode 2, ofCode 7, ofCode 7]
private theorem b_from_xyStep7 : b_from_xyPrefix6 * xInverse = b_from_xyPrefix7 := by decide +kernel
private theorem b_from_xyStep8 : b_from_xyPrefix7 * xInverse = bMatrix := by decide +kernel
theorem b_from_xy : x * x * y⁻¹ * x * y * x⁻¹ * y⁻¹ * x⁻¹ * x⁻¹ = b := by
  apply Units.ext
  change xMatrix * xMatrix * yInverse * xMatrix * yMatrix * xInverse * yInverse * xInverse * xInverse = bMatrix
  rw [b_from_xyStep1, b_from_xyStep2, b_from_xyStep3, b_from_xyStep4, b_from_xyStep5, b_from_xyStep6, b_from_xyStep7, b_from_xyStep8]

private def ad_from_cbPrefix1 : M := !![ofCode 6, ofCode 2, ofCode 3, ofCode 1; ofCode 0, ofCode 7, ofCode 1, ofCode 0; ofCode 3, ofCode 1, ofCode 0, ofCode 0; ofCode 1, ofCode 0, ofCode 0, ofCode 0]
private theorem ad_from_cbStep1 : bInverse * cMatrix = ad_from_cbPrefix1 := by decide +kernel
private def ad_from_cbPrefix2 : M := !![ofCode 6, ofCode 3, ofCode 1, ofCode 6; ofCode 0, ofCode 7, ofCode 2, ofCode 3; ofCode 3, ofCode 4, ofCode 1, ofCode 1; ofCode 1, ofCode 3, ofCode 2, ofCode 6]
private theorem ad_from_cbStep2 : ad_from_cbPrefix1 * bInverse = ad_from_cbPrefix2 := by decide +kernel
private def ad_from_cbPrefix3 : M := !![ofCode 6, ofCode 1, ofCode 3, ofCode 6; ofCode 3, ofCode 2, ofCode 7, ofCode 0; ofCode 1, ofCode 1, ofCode 4, ofCode 3; ofCode 6, ofCode 2, ofCode 3, ofCode 1]
private theorem ad_from_cbStep3 : ad_from_cbPrefix2 * cMatrix = ad_from_cbPrefix3 := by decide +kernel
private def ad_from_cbPrefix4 : M := !![ofCode 6, ofCode 0, ofCode 4, ofCode 3; ofCode 3, ofCode 7, ofCode 2, ofCode 7; ofCode 1, ofCode 2, ofCode 3, ofCode 0; ofCode 6, ofCode 3, ofCode 6, ofCode 2]
private theorem ad_from_cbStep4 : ad_from_cbPrefix3 * bMatrix = ad_from_cbPrefix4 := by decide +kernel
private def ad_from_cbPrefix5 : M := !![ofCode 3, ofCode 4, ofCode 0, ofCode 6; ofCode 7, ofCode 2, ofCode 7, ofCode 3; ofCode 0, ofCode 3, ofCode 2, ofCode 1; ofCode 2, ofCode 6, ofCode 3, ofCode 6]
private theorem ad_from_cbStep5 : ad_from_cbPrefix4 * cMatrix = ad_from_cbPrefix5 := by decide +kernel
private def ad_from_cbPrefix6 : M := !![ofCode 3, ofCode 1, ofCode 1, ofCode 4; ofCode 7, ofCode 0, ofCode 2, ofCode 1; ofCode 0, ofCode 3, ofCode 0, ofCode 1; ofCode 2, ofCode 0, ofCode 7, ofCode 3]
private theorem ad_from_cbStep6 : ad_from_cbPrefix5 * bMatrix = ad_from_cbPrefix6 := by decide +kernel
private def ad_from_cbPrefix7 : M := !![ofCode 3, ofCode 4, ofCode 6, ofCode 4; ofCode 7, ofCode 2, ofCode 2, ofCode 3; ofCode 0, ofCode 3, ofCode 2, ofCode 7; ofCode 2, ofCode 6, ofCode 7, ofCode 6]
private theorem ad_from_cbStep7 : ad_from_cbPrefix6 * bMatrix = ad_from_cbPrefix7 := by decide +kernel
private def ad_from_cbPrefix8 : M := !![ofCode 4, ofCode 6, ofCode 4, ofCode 3; ofCode 3, ofCode 2, ofCode 2, ofCode 7; ofCode 7, ofCode 2, ofCode 3, ofCode 0; ofCode 6, ofCode 7, ofCode 6, ofCode 2]
private theorem ad_from_cbStep8 : ad_from_cbPrefix7 * cMatrix = ad_from_cbPrefix8 := by decide +kernel
private def ad_from_cbPrefix9 : M := !![ofCode 4, ofCode 1, ofCode 3, ofCode 1; ofCode 3, ofCode 7, ofCode 1, ofCode 0; ofCode 7, ofCode 0, ofCode 3, ofCode 1; ofCode 6, ofCode 6, ofCode 2, ofCode 1]
private theorem ad_from_cbStep9 : ad_from_cbPrefix8 * bInverse = ad_from_cbPrefix9 := by decide +kernel
private def ad_from_cbPrefix10 : M := !![ofCode 1, ofCode 3, ofCode 1, ofCode 4; ofCode 0, ofCode 1, ofCode 7, ofCode 3; ofCode 1, ofCode 3, ofCode 0, ofCode 7; ofCode 1, ofCode 2, ofCode 6, ofCode 6]
private theorem ad_from_cbStep10 : ad_from_cbPrefix9 * cMatrix = ad_from_cbPrefix10 := by decide +kernel
private def ad_from_cbPrefix11 : M := !![ofCode 1, ofCode 0, ofCode 3, ofCode 7; ofCode 0, ofCode 1, ofCode 0, ofCode 3; ofCode 1, ofCode 0, ofCode 2, ofCode 7; ofCode 1, ofCode 1, ofCode 3, ofCode 5]
private theorem ad_from_cbStep11 : ad_from_cbPrefix10 * bMatrix = ad_from_cbPrefix11 := by decide +kernel
private def ad_from_cbPrefix12 : M := !![ofCode 7, ofCode 3, ofCode 0, ofCode 1; ofCode 3, ofCode 0, ofCode 1, ofCode 0; ofCode 7, ofCode 2, ofCode 0, ofCode 1; ofCode 5, ofCode 3, ofCode 1, ofCode 1]
private theorem ad_from_cbStep12 : ad_from_cbPrefix11 * cMatrix = ad_from_cbPrefix12 := by decide +kernel
private def ad_from_cbPrefix13 : M := !![ofCode 7, ofCode 1, ofCode 7, ofCode 5; ofCode 3, ofCode 5, ofCode 7, ofCode 2; ofCode 7, ofCode 0, ofCode 0, ofCode 5; ofCode 5, ofCode 7, ofCode 2, ofCode 1]
private theorem ad_from_cbStep13 : ad_from_cbPrefix12 * bInverse = ad_from_cbPrefix13 := by decide +kernel
private def ad_from_cbPrefix14 : M := !![ofCode 5, ofCode 7, ofCode 1, ofCode 7; ofCode 2, ofCode 7, ofCode 5, ofCode 3; ofCode 5, ofCode 0, ofCode 0, ofCode 7; ofCode 1, ofCode 2, ofCode 7, ofCode 5]
private theorem ad_from_cbStep14 : ad_from_cbPrefix13 * cMatrix = ad_from_cbPrefix14 := by decide +kernel
private def ad_from_cbPrefix15 : M := !![ofCode 5, ofCode 3, ofCode 2, ofCode 2; ofCode 2, ofCode 1, ofCode 6, ofCode 5; ofCode 5, ofCode 4, ofCode 0, ofCode 4; ofCode 1, ofCode 1, ofCode 2, ofCode 5]
private theorem ad_from_cbStep15 : ad_from_cbPrefix14 * bMatrix = ad_from_cbPrefix15 := by decide +kernel
private def ad_from_cbPrefix16 : M := !![ofCode 2, ofCode 2, ofCode 3, ofCode 5; ofCode 5, ofCode 6, ofCode 1, ofCode 2; ofCode 4, ofCode 0, ofCode 4, ofCode 5; ofCode 5, ofCode 2, ofCode 1, ofCode 1]
private theorem ad_from_cbStep16 : ad_from_cbPrefix15 * cMatrix = ad_from_cbPrefix16 := by decide +kernel
private def ad_from_cbPrefix17 : M := !![ofCode 2, ofCode 4, ofCode 2, ofCode 7; ofCode 5, ofCode 2, ofCode 4, ofCode 2; ofCode 4, ofCode 7, ofCode 7, ofCode 7; ofCode 5, ofCode 6, ofCode 5, ofCode 1]
private theorem ad_from_cbStep17 : ad_from_cbPrefix16 * bInverse = ad_from_cbPrefix17 := by decide +kernel
private def ad_from_cbPrefix18 : M := !![ofCode 7, ofCode 2, ofCode 4, ofCode 2; ofCode 2, ofCode 4, ofCode 2, ofCode 5; ofCode 7, ofCode 7, ofCode 7, ofCode 4; ofCode 1, ofCode 5, ofCode 6, ofCode 5]
private theorem ad_from_cbStep18 : ad_from_cbPrefix17 * cMatrix = ad_from_cbPrefix18 := by decide +kernel
private def ad_from_cbPrefix19 : M := !![ofCode 7, ofCode 0, ofCode 1, ofCode 5; ofCode 2, ofCode 2, ofCode 3, ofCode 7; ofCode 7, ofCode 5, ofCode 4, ofCode 7; ofCode 1, ofCode 6, ofCode 0, ofCode 3]
private theorem ad_from_cbStep19 : ad_from_cbPrefix18 * bMatrix = ad_from_cbPrefix19 := by decide +kernel
private def ad_from_cbPrefix20 : M := !![ofCode 7, ofCode 2, ofCode 1, ofCode 2; ofCode 2, ofCode 4, ofCode 6, ofCode 1; ofCode 7, ofCode 7, ofCode 2, ofCode 5; ofCode 1, ofCode 5, ofCode 4, ofCode 2]
private theorem ad_from_cbStep20 : ad_from_cbPrefix19 * bMatrix = ad_from_cbPrefix20 := by decide +kernel
private def ad_from_cbPrefix21 : M := !![ofCode 2, ofCode 1, ofCode 2, ofCode 7; ofCode 1, ofCode 6, ofCode 4, ofCode 2; ofCode 5, ofCode 2, ofCode 7, ofCode 7; ofCode 2, ofCode 4, ofCode 5, ofCode 1]
private theorem ad_from_cbStep21 : ad_from_cbPrefix20 * cMatrix = ad_from_cbPrefix21 := by decide +kernel
private def ad_from_cbPrefix22 : M := !![ofCode 2, ofCode 7, ofCode 1, ofCode 6; ofCode 1, ofCode 5, ofCode 2, ofCode 3; ofCode 5, ofCode 6, ofCode 3, ofCode 6; ofCode 2, ofCode 2, ofCode 0, ofCode 2]
private theorem ad_from_cbStep22 : ad_from_cbPrefix21 * bInverse = ad_from_cbPrefix22 := by decide +kernel
private def ad_from_cbPrefix23 : M := !![ofCode 6, ofCode 1, ofCode 7, ofCode 2; ofCode 3, ofCode 2, ofCode 5, ofCode 1; ofCode 6, ofCode 3, ofCode 6, ofCode 5; ofCode 2, ofCode 0, ofCode 2, ofCode 2]
private theorem ad_from_cbStep23 : ad_from_cbPrefix22 * cMatrix = ad_from_cbPrefix23 := by decide +kernel
private def ad_from_cbPrefix24 : M := !![ofCode 6, ofCode 0, ofCode 0, ofCode 0; ofCode 3, ofCode 7, ofCode 0, ofCode 0; ofCode 6, ofCode 2, ofCode 4, ofCode 0; ofCode 2, ofCode 6, ofCode 2, ofCode 3]
private theorem ad_from_cbStep24 : ad_from_cbPrefix23 * bMatrix = ad_from_cbPrefix24 := by decide +kernel
private def ad_from_cbPrefix25 : M := !![ofCode 0, ofCode 0, ofCode 0, ofCode 6; ofCode 0, ofCode 0, ofCode 7, ofCode 3; ofCode 0, ofCode 4, ofCode 2, ofCode 6; ofCode 3, ofCode 2, ofCode 6, ofCode 2]
private theorem ad_from_cbStep25 : ad_from_cbPrefix24 * cMatrix = ad_from_cbPrefix25 := by decide +kernel
private def ad_from_cbPrefix26 : M := !![ofCode 0, ofCode 0, ofCode 0, ofCode 6; ofCode 0, ofCode 0, ofCode 7, ofCode 1; ofCode 0, ofCode 4, ofCode 3, ofCode 0; ofCode 3, ofCode 7, ofCode 5, ofCode 2]
private theorem ad_from_cbStep26 : ad_from_cbPrefix25 * bInverse = ad_from_cbPrefix26 := by decide +kernel
private def ad_from_cbPrefix27 : M := !![ofCode 6, ofCode 0, ofCode 0, ofCode 0; ofCode 1, ofCode 7, ofCode 0, ofCode 0; ofCode 0, ofCode 3, ofCode 4, ofCode 0; ofCode 2, ofCode 5, ofCode 7, ofCode 3]
private theorem ad_from_cbStep27 : ad_from_cbPrefix26 * cMatrix = ad_from_cbPrefix27 := by decide +kernel
private def ad_from_cbPrefix28 : M := !![ofCode 6, ofCode 1, ofCode 0, ofCode 2; ofCode 1, ofCode 4, ofCode 3, ofCode 3; ofCode 0, ofCode 3, ofCode 6, ofCode 1; ofCode 2, ofCode 3, ofCode 1, ofCode 7]
private theorem ad_from_cbStep28 : ad_from_cbPrefix27 * bMatrix = ad_from_cbPrefix28 := by decide +kernel
private theorem ad_from_cbStep29 : ad_from_cbPrefix28 * cMatrix = adMatrix := by decide +kernel
theorem ad_from_cb : b⁻¹ * c * b⁻¹ * c * b * c * b * b * c * b⁻¹ * c * b * c * b⁻¹ * c * b * c * b⁻¹ * c * b * b * c * b⁻¹ * c * b * c * b⁻¹ * c * b * c = ad := by
  apply Units.ext
  change bInverse * cMatrix * bInverse * cMatrix * bMatrix * cMatrix * bMatrix * bMatrix * cMatrix * bInverse * cMatrix * bMatrix * cMatrix * bInverse * cMatrix * bMatrix * cMatrix * bInverse * cMatrix * bMatrix * bMatrix * cMatrix * bInverse * cMatrix * bMatrix * cMatrix * bInverse * cMatrix * bMatrix * cMatrix = adMatrix
  rw [ad_from_cbStep1, ad_from_cbStep2, ad_from_cbStep3, ad_from_cbStep4, ad_from_cbStep5, ad_from_cbStep6, ad_from_cbStep7, ad_from_cbStep8, ad_from_cbStep9, ad_from_cbStep10, ad_from_cbStep11, ad_from_cbStep12, ad_from_cbStep13, ad_from_cbStep14, ad_from_cbStep15, ad_from_cbStep16, ad_from_cbStep17, ad_from_cbStep18, ad_from_cbStep19, ad_from_cbStep20, ad_from_cbStep21, ad_from_cbStep22, ad_from_cbStep23, ad_from_cbStep24, ad_from_cbStep25, ad_from_cbStep26, ad_from_cbStep27, ad_from_cbStep28, ad_from_cbStep29]

private def bd_from_cbPrefix1 : M := !![ofCode 1, ofCode 0, ofCode 2, ofCode 6; ofCode 0, ofCode 1, ofCode 0, ofCode 2; ofCode 0, ofCode 0, ofCode 1, ofCode 0; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem bd_from_cbStep1 : bMatrix * bMatrix = bd_from_cbPrefix1 := by decide +kernel
private def bd_from_cbPrefix2 : M := !![ofCode 6, ofCode 2, ofCode 0, ofCode 1; ofCode 2, ofCode 0, ofCode 1, ofCode 0; ofCode 0, ofCode 1, ofCode 0, ofCode 0; ofCode 1, ofCode 0, ofCode 0, ofCode 0]
private theorem bd_from_cbStep2 : bd_from_cbPrefix1 * cMatrix = bd_from_cbPrefix2 := by decide +kernel
private def bd_from_cbPrefix3 : M := !![ofCode 6, ofCode 3, ofCode 5, ofCode 7; ofCode 2, ofCode 6, ofCode 1, ofCode 4; ofCode 0, ofCode 1, ofCode 7, ofCode 2; ofCode 1, ofCode 3, ofCode 0, ofCode 6]
private theorem bd_from_cbStep3 : bd_from_cbPrefix2 * bMatrix = bd_from_cbPrefix3 := by decide +kernel
private def bd_from_cbPrefix4 : M := !![ofCode 7, ofCode 5, ofCode 3, ofCode 6; ofCode 4, ofCode 1, ofCode 6, ofCode 2; ofCode 2, ofCode 7, ofCode 1, ofCode 0; ofCode 6, ofCode 0, ofCode 3, ofCode 1]
private theorem bd_from_cbStep4 : bd_from_cbPrefix3 * cMatrix = bd_from_cbPrefix4 := by decide +kernel
private def bd_from_cbPrefix5 : M := !![ofCode 7, ofCode 7, ofCode 5, ofCode 6; ofCode 4, ofCode 6, ofCode 1, ofCode 4; ofCode 2, ofCode 1, ofCode 2, ofCode 1; ofCode 6, ofCode 1, ofCode 3, ofCode 6]
private theorem bd_from_cbStep5 : bd_from_cbPrefix4 * bMatrix = bd_from_cbPrefix5 := by decide +kernel
private def bd_from_cbPrefix6 : M := !![ofCode 7, ofCode 5, ofCode 6, ofCode 3; ofCode 4, ofCode 1, ofCode 5, ofCode 5; ofCode 2, ofCode 7, ofCode 5, ofCode 2; ofCode 6, ofCode 0, ofCode 4, ofCode 3]
private theorem bd_from_cbStep6 : bd_from_cbPrefix5 * bMatrix = bd_from_cbPrefix6 := by decide +kernel
private def bd_from_cbPrefix7 : M := !![ofCode 3, ofCode 6, ofCode 5, ofCode 7; ofCode 5, ofCode 5, ofCode 1, ofCode 4; ofCode 2, ofCode 5, ofCode 7, ofCode 2; ofCode 3, ofCode 4, ofCode 0, ofCode 6]
private theorem bd_from_cbStep7 : bd_from_cbPrefix6 * cMatrix = bd_from_cbPrefix7 := by decide +kernel
private def bd_from_cbPrefix8 : M := !![ofCode 3, ofCode 3, ofCode 7, ofCode 2; ofCode 5, ofCode 1, ofCode 6, ofCode 4; ofCode 2, ofCode 3, ofCode 5, ofCode 7; ofCode 3, ofCode 1, ofCode 7, ofCode 7]
private theorem bd_from_cbStep8 : bd_from_cbPrefix7 * bInverse = bd_from_cbPrefix8 := by decide +kernel
private def bd_from_cbPrefix9 : M := !![ofCode 2, ofCode 7, ofCode 3, ofCode 3; ofCode 4, ofCode 6, ofCode 1, ofCode 5; ofCode 7, ofCode 5, ofCode 3, ofCode 2; ofCode 7, ofCode 7, ofCode 1, ofCode 3]
private theorem bd_from_cbStep9 : bd_from_cbPrefix8 * cMatrix = bd_from_cbPrefix9 := by decide +kernel
private def bd_from_cbPrefix10 : M := !![ofCode 2, ofCode 1, ofCode 0, ofCode 4; ofCode 4, ofCode 1, ofCode 5, ofCode 4; ofCode 7, ofCode 7, ofCode 5, ofCode 2; ofCode 7, ofCode 5, ofCode 2, ofCode 1]
private theorem bd_from_cbStep10 : bd_from_cbPrefix9 * bMatrix = bd_from_cbPrefix10 := by decide +kernel
private def bd_from_cbPrefix11 : M := !![ofCode 2, ofCode 7, ofCode 7, ofCode 1; ofCode 4, ofCode 6, ofCode 2, ofCode 7; ofCode 7, ofCode 5, ofCode 6, ofCode 7; ofCode 7, ofCode 7, ofCode 4, ofCode 2]
private theorem bd_from_cbStep11 : bd_from_cbPrefix10 * bMatrix = bd_from_cbPrefix11 := by decide +kernel
private def bd_from_cbPrefix12 : M := !![ofCode 1, ofCode 7, ofCode 7, ofCode 2; ofCode 7, ofCode 2, ofCode 6, ofCode 4; ofCode 7, ofCode 6, ofCode 5, ofCode 7; ofCode 2, ofCode 4, ofCode 7, ofCode 7]
private theorem bd_from_cbStep12 : bd_from_cbPrefix11 * cMatrix = bd_from_cbPrefix12 := by decide +kernel
private def bd_from_cbPrefix13 : M := !![ofCode 1, ofCode 4, ofCode 4, ofCode 3; ofCode 7, ofCode 0, ofCode 3, ofCode 5; ofCode 7, ofCode 4, ofCode 1, ofCode 0; ofCode 2, ofCode 2, ofCode 6, ofCode 1]
private theorem bd_from_cbStep13 : bd_from_cbPrefix12 * bMatrix = bd_from_cbPrefix13 := by decide +kernel
private def bd_from_cbPrefix14 : M := !![ofCode 3, ofCode 4, ofCode 4, ofCode 1; ofCode 5, ofCode 3, ofCode 0, ofCode 7; ofCode 0, ofCode 1, ofCode 4, ofCode 7; ofCode 1, ofCode 6, ofCode 2, ofCode 2]
private theorem bd_from_cbStep14 : bd_from_cbPrefix13 * cMatrix = bd_from_cbPrefix14 := by decide +kernel
private def bd_from_cbPrefix15 : M := !![ofCode 3, ofCode 1, ofCode 3, ofCode 7; ofCode 5, ofCode 7, ofCode 3, ofCode 4; ofCode 0, ofCode 1, ofCode 3, ofCode 0; ofCode 1, ofCode 5, ofCode 4, ofCode 2]
private theorem bd_from_cbStep15 : bd_from_cbPrefix14 * bInverse = bd_from_cbPrefix15 := by decide +kernel
private def bd_from_cbPrefix16 : M := !![ofCode 7, ofCode 3, ofCode 1, ofCode 3; ofCode 4, ofCode 3, ofCode 7, ofCode 5; ofCode 0, ofCode 3, ofCode 1, ofCode 0; ofCode 2, ofCode 4, ofCode 5, ofCode 1]
private theorem bd_from_cbStep16 : bd_from_cbPrefix15 * cMatrix = bd_from_cbPrefix16 := by decide +kernel
private def bd_from_cbPrefix17 : M := !![ofCode 7, ofCode 1, ofCode 3, ofCode 2; ofCode 4, ofCode 4, ofCode 5, ofCode 4; ofCode 0, ofCode 3, ofCode 3, ofCode 5; ofCode 2, ofCode 2, ofCode 4, ofCode 1]
private theorem bd_from_cbStep17 : bd_from_cbPrefix16 * bMatrix = bd_from_cbPrefix17 := by decide +kernel
private def bd_from_cbPrefix18 : M := !![ofCode 7, ofCode 3, ofCode 4, ofCode 1; ofCode 4, ofCode 3, ofCode 4, ofCode 6; ofCode 0, ofCode 3, ofCode 1, ofCode 6; ofCode 2, ofCode 4, ofCode 1, ofCode 5]
private theorem bd_from_cbStep18 : bd_from_cbPrefix17 * bMatrix = bd_from_cbPrefix18 := by decide +kernel
private def bd_from_cbPrefix19 : M := !![ofCode 1, ofCode 4, ofCode 3, ofCode 7; ofCode 6, ofCode 4, ofCode 3, ofCode 4; ofCode 6, ofCode 1, ofCode 3, ofCode 0; ofCode 5, ofCode 1, ofCode 4, ofCode 2]
private theorem bd_from_cbStep19 : bd_from_cbPrefix18 * cMatrix = bd_from_cbPrefix19 := by decide +kernel
private def bd_from_cbPrefix20 : M := !![ofCode 1, ofCode 7, ofCode 0, ofCode 4; ofCode 6, ofCode 5, ofCode 5, ofCode 3; ofCode 6, ofCode 0, ofCode 3, ofCode 7; ofCode 5, ofCode 5, ofCode 2, ofCode 6]
private theorem bd_from_cbStep20 : bd_from_cbPrefix19 * bInverse = bd_from_cbPrefix20 := by decide +kernel
private def bd_from_cbPrefix21 : M := !![ofCode 4, ofCode 0, ofCode 7, ofCode 1; ofCode 3, ofCode 5, ofCode 5, ofCode 6; ofCode 7, ofCode 3, ofCode 0, ofCode 6; ofCode 6, ofCode 2, ofCode 5, ofCode 5]
private theorem bd_from_cbStep21 : bd_from_cbPrefix20 * cMatrix = bd_from_cbPrefix21 := by decide +kernel
private def bd_from_cbPrefix22 : M := !![ofCode 4, ofCode 7, ofCode 7, ofCode 6; ofCode 3, ofCode 0, ofCode 3, ofCode 2; ofCode 7, ofCode 1, ofCode 2, ofCode 4; ofCode 6, ofCode 3, ofCode 0, ofCode 7]
private theorem bd_from_cbStep22 : bd_from_cbPrefix21 * bMatrix = bd_from_cbPrefix22 := by decide +kernel
private def bd_from_cbPrefix23 : M := !![ofCode 4, ofCode 0, ofCode 4, ofCode 4; ofCode 3, ofCode 5, ofCode 3, ofCode 6; ofCode 7, ofCode 3, ofCode 5, ofCode 4; ofCode 6, ofCode 2, ofCode 2, ofCode 3]
private theorem bd_from_cbStep23 : bd_from_cbPrefix22 * bMatrix = bd_from_cbPrefix23 := by decide +kernel
private def bd_from_cbPrefix24 : M := !![ofCode 4, ofCode 4, ofCode 0, ofCode 4; ofCode 6, ofCode 3, ofCode 5, ofCode 3; ofCode 4, ofCode 5, ofCode 3, ofCode 7; ofCode 3, ofCode 2, ofCode 2, ofCode 6]
private theorem bd_from_cbStep24 : bd_from_cbPrefix23 * cMatrix = bd_from_cbPrefix24 := by decide +kernel
private def bd_from_cbPrefix25 : M := !![ofCode 4, ofCode 3, ofCode 1, ofCode 2; ofCode 6, ofCode 2, ofCode 7, ofCode 3; ofCode 4, ofCode 2, ofCode 5, ofCode 6; ofCode 3, ofCode 7, ofCode 7, ofCode 5]
private theorem bd_from_cbStep25 : bd_from_cbPrefix24 * bMatrix = bd_from_cbPrefix25 := by decide +kernel
private def bd_from_cbPrefix26 : M := !![ofCode 2, ofCode 1, ofCode 3, ofCode 4; ofCode 3, ofCode 7, ofCode 2, ofCode 6; ofCode 6, ofCode 5, ofCode 2, ofCode 4; ofCode 5, ofCode 7, ofCode 7, ofCode 3]
private theorem bd_from_cbStep26 : bd_from_cbPrefix25 * cMatrix = bd_from_cbPrefix26 := by decide +kernel
private def bd_from_cbPrefix27 : M := !![ofCode 2, ofCode 7, ofCode 0, ofCode 6; ofCode 3, ofCode 2, ofCode 7, ofCode 1; ofCode 6, ofCode 4, ofCode 3, ofCode 0; ofCode 5, ofCode 3, ofCode 5, ofCode 2]
private theorem bd_from_cbStep27 : bd_from_cbPrefix26 * bInverse = bd_from_cbPrefix27 := by decide +kernel
private theorem bd_from_cbStep28 : bd_from_cbPrefix27 * cMatrix = bdMatrix := by decide +kernel
theorem bd_from_cb : b * b * c * b * c * b * b * c * b⁻¹ * c * b * b * c * b * c * b⁻¹ * c * b * b * c * b⁻¹ * c * b * b * c * b * c * b⁻¹ * c = bd := by
  apply Units.ext
  change bMatrix * bMatrix * cMatrix * bMatrix * cMatrix * bMatrix * bMatrix * cMatrix * bInverse * cMatrix * bMatrix * bMatrix * cMatrix * bMatrix * cMatrix * bInverse * cMatrix * bMatrix * bMatrix * cMatrix * bInverse * cMatrix * bMatrix * bMatrix * cMatrix * bMatrix * cMatrix * bInverse * cMatrix = bdMatrix
  rw [bd_from_cbStep1, bd_from_cbStep2, bd_from_cbStep3, bd_from_cbStep4, bd_from_cbStep5, bd_from_cbStep6, bd_from_cbStep7, bd_from_cbStep8, bd_from_cbStep9, bd_from_cbStep10, bd_from_cbStep11, bd_from_cbStep12, bd_from_cbStep13, bd_from_cbStep14, bd_from_cbStep15, bd_from_cbStep16, bd_from_cbStep17, bd_from_cbStep18, bd_from_cbStep19, bd_from_cbStep20, bd_from_cbStep21, bd_from_cbStep22, bd_from_cbStep23, bd_from_cbStep24, bd_from_cbStep25, bd_from_cbStep26, bd_from_cbStep27, bd_from_cbStep28]

private def x_seventhPrefix1 : M := !![ofCode 7, ofCode 7, ofCode 7, ofCode 7; ofCode 7, ofCode 5, ofCode 5, ofCode 7; ofCode 7, ofCode 5, ofCode 0, ofCode 2; ofCode 7, ofCode 7, ofCode 2, ofCode 6]
private theorem x_seventhStep1 : xMatrix * xMatrix = x_seventhPrefix1 := by decide +kernel
private def x_seventhPrefix2 : M := !![ofCode 6, ofCode 2, ofCode 0, ofCode 1; ofCode 2, ofCode 0, ofCode 1, ofCode 0; ofCode 0, ofCode 1, ofCode 0, ofCode 0; ofCode 1, ofCode 0, ofCode 0, ofCode 0]
private theorem x_seventhStep2 : x_seventhPrefix1 * xMatrix = x_seventhPrefix2 := by decide +kernel
private def x_seventhPrefix3 : M := !![ofCode 0, ofCode 0, ofCode 0, ofCode 1; ofCode 0, ofCode 0, ofCode 1, ofCode 0; ofCode 0, ofCode 1, ofCode 0, ofCode 2; ofCode 1, ofCode 0, ofCode 2, ofCode 6]
private theorem x_seventhStep3 : x_seventhPrefix2 * xMatrix = x_seventhPrefix3 := by decide +kernel
private def x_seventhPrefix4 : M := !![ofCode 6, ofCode 2, ofCode 7, ofCode 7; ofCode 2, ofCode 0, ofCode 5, ofCode 7; ofCode 7, ofCode 5, ofCode 5, ofCode 7; ofCode 7, ofCode 7, ofCode 7, ofCode 7]
private theorem x_seventhStep4 : x_seventhPrefix3 * xMatrix = x_seventhPrefix4 := by decide +kernel
private def x_seventhPrefix5 : M := !![ofCode 7, ofCode 7, ofCode 2, ofCode 6; ofCode 7, ofCode 5, ofCode 0, ofCode 2; ofCode 2, ofCode 0, ofCode 1, ofCode 0; ofCode 6, ofCode 2, ofCode 0, ofCode 1]
private theorem x_seventhStep5 : x_seventhPrefix4 * xMatrix = x_seventhPrefix5 := by decide +kernel
private theorem x_seventhStep6 : x_seventhPrefix5 * xMatrix = (1 : M) := by decide +kernel
theorem x_seventh : x * x * x * x * x * x * x = (1 : UnitMatrix) := by
  apply Units.ext
  change xMatrix * xMatrix * xMatrix * xMatrix * xMatrix * xMatrix * xMatrix = (1 : M)
  rw [x_seventhStep1, x_seventhStep2, x_seventhStep3, x_seventhStep4, x_seventhStep5, x_seventhStep6]

theorem outer_c : outerAut c = ad := by
  apply Units.ext
  exact SuzukiEightCoverSemilinear.c_semilinear

theorem outer_b : outerAut b = bd := by
  apply Units.ext
  exact SuzukiEightCoverSemilinear.b_semilinear

def cAut : MulAut UnitMatrix := MulAut.conj c⁻¹

def outputPrefix0Matrix : M := !![ofCode 7, ofCode 7, ofCode 2, ofCode 6; ofCode 7, ofCode 5, ofCode 0, ofCode 2; ofCode 2, ofCode 0, ofCode 1, ofCode 0; ofCode 6, ofCode 2, ofCode 0, ofCode 1]
def outputPrefix0Inverse : M := !![ofCode 1, ofCode 0, ofCode 2, ofCode 6; ofCode 0, ofCode 1, ofCode 0, ofCode 2; ofCode 2, ofCode 0, ofCode 5, ofCode 7; ofCode 6, ofCode 2, ofCode 7, ofCode 7]
theorem outputPrefix0_mul_inverse : outputPrefix0Matrix * outputPrefix0Inverse = 1 := by decide +kernel
theorem outputPrefix0_inverse_mul : outputPrefix0Inverse * outputPrefix0Matrix = 1 := by decide +kernel
def outputPrefix0 : UnitMatrix := ⟨outputPrefix0Matrix, outputPrefix0Inverse, outputPrefix0_mul_inverse, outputPrefix0_inverse_mul⟩

private theorem outputStep0 : cAut x = outputPrefix0 := by decide +kernel

def outputPrefix1Matrix : M := !![ofCode 4, ofCode 2, ofCode 6, ofCode 3; ofCode 4, ofCode 7, ofCode 2, ofCode 3; ofCode 6, ofCode 6, ofCode 3, ofCode 6; ofCode 1, ofCode 2, ofCode 4, ofCode 4]
def outputPrefix1Inverse : M := !![ofCode 4, ofCode 6, ofCode 3, ofCode 3; ofCode 4, ofCode 3, ofCode 2, ofCode 6; ofCode 2, ofCode 6, ofCode 7, ofCode 2; ofCode 1, ofCode 6, ofCode 4, ofCode 4]
theorem outputPrefix1_mul_inverse : outputPrefix1Matrix * outputPrefix1Inverse = 1 := by decide +kernel
theorem outputPrefix1_inverse_mul : outputPrefix1Inverse * outputPrefix1Matrix = 1 := by decide +kernel
def outputPrefix1 : UnitMatrix := ⟨outputPrefix1Matrix, outputPrefix1Inverse, outputPrefix1_mul_inverse, outputPrefix1_inverse_mul⟩

private theorem outputStep1 : outerAut.symm outputPrefix0 = outputPrefix1 := by decide +kernel

def outputPrefix2Matrix : M := !![ofCode 4, ofCode 4, ofCode 2, ofCode 1; ofCode 6, ofCode 3, ofCode 6, ofCode 6; ofCode 3, ofCode 2, ofCode 7, ofCode 4; ofCode 3, ofCode 6, ofCode 2, ofCode 4]
def outputPrefix2Inverse : M := !![ofCode 4, ofCode 4, ofCode 6, ofCode 1; ofCode 2, ofCode 7, ofCode 6, ofCode 2; ofCode 6, ofCode 2, ofCode 3, ofCode 4; ofCode 3, ofCode 3, ofCode 6, ofCode 4]
theorem outputPrefix2_mul_inverse : outputPrefix2Matrix * outputPrefix2Inverse = 1 := by decide +kernel
theorem outputPrefix2_inverse_mul : outputPrefix2Inverse * outputPrefix2Matrix = 1 := by decide +kernel
def outputPrefix2 : UnitMatrix := ⟨outputPrefix2Matrix, outputPrefix2Inverse, outputPrefix2_mul_inverse, outputPrefix2_inverse_mul⟩

private theorem outputStep2 : cAut outputPrefix1 = outputPrefix2 := by decide +kernel

def outputPrefix3Matrix : M := !![ofCode 7, ofCode 2, ofCode 1, ofCode 2; ofCode 2, ofCode 4, ofCode 6, ofCode 1; ofCode 5, ofCode 1, ofCode 1, ofCode 3; ofCode 4, ofCode 7, ofCode 2, ofCode 4]
def outputPrefix3Inverse : M := !![ofCode 4, ofCode 3, ofCode 1, ofCode 2; ofCode 2, ofCode 1, ofCode 6, ofCode 1; ofCode 7, ofCode 1, ofCode 4, ofCode 2; ofCode 4, ofCode 5, ofCode 2, ofCode 7]
theorem outputPrefix3_mul_inverse : outputPrefix3Matrix * outputPrefix3Inverse = 1 := by decide +kernel
theorem outputPrefix3_inverse_mul : outputPrefix3Inverse * outputPrefix3Matrix = 1 := by decide +kernel
def outputPrefix3 : UnitMatrix := ⟨outputPrefix3Matrix, outputPrefix3Inverse, outputPrefix3_mul_inverse, outputPrefix3_inverse_mul⟩

private theorem outputStep3 : outerAut.symm outputPrefix2 = outputPrefix3 := by decide +kernel

def outputPrefix4Matrix : M := !![ofCode 4, ofCode 2, ofCode 7, ofCode 4; ofCode 3, ofCode 1, ofCode 1, ofCode 5; ofCode 1, ofCode 6, ofCode 4, ofCode 2; ofCode 2, ofCode 1, ofCode 2, ofCode 7]
def outputPrefix4Inverse : M := !![ofCode 7, ofCode 2, ofCode 5, ofCode 4; ofCode 2, ofCode 4, ofCode 1, ofCode 7; ofCode 1, ofCode 6, ofCode 1, ofCode 2; ofCode 2, ofCode 1, ofCode 3, ofCode 4]
theorem outputPrefix4_mul_inverse : outputPrefix4Matrix * outputPrefix4Inverse = 1 := by decide +kernel
theorem outputPrefix4_inverse_mul : outputPrefix4Inverse * outputPrefix4Matrix = 1 := by decide +kernel
def outputPrefix4 : UnitMatrix := ⟨outputPrefix4Matrix, outputPrefix4Inverse, outputPrefix4_mul_inverse, outputPrefix4_inverse_mul⟩

private theorem outputStep4 : cAut outputPrefix3 = outputPrefix4 := by decide +kernel

def outputPrefix5Matrix : M := !![ofCode 1, ofCode 3, ofCode 4, ofCode 3; ofCode 2, ofCode 7, ofCode 4, ofCode 0; ofCode 0, ofCode 6, ofCode 5, ofCode 1; ofCode 5, ofCode 3, ofCode 3, ofCode 7]
def outputPrefix5Inverse : M := !![ofCode 7, ofCode 1, ofCode 0, ofCode 3; ofCode 3, ofCode 5, ofCode 4, ofCode 4; ofCode 3, ofCode 6, ofCode 7, ofCode 3; ofCode 5, ofCode 0, ofCode 2, ofCode 1]
theorem outputPrefix5_mul_inverse : outputPrefix5Matrix * outputPrefix5Inverse = 1 := by decide +kernel
theorem outputPrefix5_inverse_mul : outputPrefix5Inverse * outputPrefix5Matrix = 1 := by decide +kernel
def outputPrefix5 : UnitMatrix := ⟨outputPrefix5Matrix, outputPrefix5Inverse, outputPrefix5_mul_inverse, outputPrefix5_inverse_mul⟩

private theorem outputStep5 : outerAut outputPrefix4 = outputPrefix5 := by decide +kernel

def outputPrefix6Matrix : M := !![ofCode 7, ofCode 3, ofCode 3, ofCode 5; ofCode 1, ofCode 5, ofCode 6, ofCode 0; ofCode 0, ofCode 4, ofCode 7, ofCode 2; ofCode 3, ofCode 4, ofCode 3, ofCode 1]
def outputPrefix6Inverse : M := !![ofCode 1, ofCode 2, ofCode 0, ofCode 5; ofCode 3, ofCode 7, ofCode 6, ofCode 3; ofCode 4, ofCode 4, ofCode 5, ofCode 3; ofCode 3, ofCode 0, ofCode 1, ofCode 7]
theorem outputPrefix6_mul_inverse : outputPrefix6Matrix * outputPrefix6Inverse = 1 := by decide +kernel
theorem outputPrefix6_inverse_mul : outputPrefix6Inverse * outputPrefix6Matrix = 1 := by decide +kernel
def outputPrefix6 : UnitMatrix := ⟨outputPrefix6Matrix, outputPrefix6Inverse, outputPrefix6_mul_inverse, outputPrefix6_inverse_mul⟩

private theorem outputStep6 : cAut outputPrefix5 = outputPrefix6 := by decide +kernel

def outputPrefix7Matrix : M := !![ofCode 3, ofCode 7, ofCode 1, ofCode 1; ofCode 1, ofCode 0, ofCode 5, ofCode 4; ofCode 1, ofCode 2, ofCode 6, ofCode 4; ofCode 4, ofCode 1, ofCode 4, ofCode 3]
def outputPrefix7Inverse : M := !![ofCode 3, ofCode 4, ofCode 4, ofCode 1; ofCode 4, ofCode 6, ofCode 5, ofCode 1; ofCode 1, ofCode 2, ofCode 0, ofCode 7; ofCode 4, ofCode 1, ofCode 1, ofCode 3]
theorem outputPrefix7_mul_inverse : outputPrefix7Matrix * outputPrefix7Inverse = 1 := by decide +kernel
theorem outputPrefix7_inverse_mul : outputPrefix7Inverse * outputPrefix7Matrix = 1 := by decide +kernel
def outputPrefix7 : UnitMatrix := ⟨outputPrefix7Matrix, outputPrefix7Inverse, outputPrefix7_mul_inverse, outputPrefix7_inverse_mul⟩

private theorem outputStep7 : outerAut.symm outputPrefix6 = outputPrefix7 := by decide +kernel

def outputPrefix8Matrix : M := !![ofCode 3, ofCode 4, ofCode 1, ofCode 4; ofCode 4, ofCode 6, ofCode 2, ofCode 1; ofCode 4, ofCode 5, ofCode 0, ofCode 1; ofCode 1, ofCode 1, ofCode 7, ofCode 3]
def outputPrefix8Inverse : M := !![ofCode 3, ofCode 1, ofCode 1, ofCode 4; ofCode 7, ofCode 0, ofCode 2, ofCode 1; ofCode 1, ofCode 5, ofCode 6, ofCode 4; ofCode 1, ofCode 4, ofCode 4, ofCode 3]
theorem outputPrefix8_mul_inverse : outputPrefix8Matrix * outputPrefix8Inverse = 1 := by decide +kernel
theorem outputPrefix8_inverse_mul : outputPrefix8Inverse * outputPrefix8Matrix = 1 := by decide +kernel
def outputPrefix8 : UnitMatrix := ⟨outputPrefix8Matrix, outputPrefix8Inverse, outputPrefix8_mul_inverse, outputPrefix8_inverse_mul⟩

private theorem outputStep8 : cAut outputPrefix7 = outputPrefix8 := by decide +kernel

def outputPrefix9Matrix : M := !![ofCode 3, ofCode 7, ofCode 3, ofCode 6; ofCode 7, ofCode 5, ofCode 4, ofCode 6; ofCode 1, ofCode 7, ofCode 0, ofCode 5; ofCode 1, ofCode 6, ofCode 4, ofCode 4]
def outputPrefix9Inverse : M := !![ofCode 4, ofCode 5, ofCode 6, ofCode 6; ofCode 4, ofCode 0, ofCode 4, ofCode 3; ofCode 6, ofCode 7, ofCode 5, ofCode 7; ofCode 1, ofCode 1, ofCode 7, ofCode 3]
theorem outputPrefix9_mul_inverse : outputPrefix9Matrix * outputPrefix9Inverse = 1 := by decide +kernel
theorem outputPrefix9_inverse_mul : outputPrefix9Inverse * outputPrefix9Matrix = 1 := by decide +kernel
def outputPrefix9 : UnitMatrix := ⟨outputPrefix9Matrix, outputPrefix9Inverse, outputPrefix9_mul_inverse, outputPrefix9_inverse_mul⟩

private theorem outputStep9 : outerAut.symm outputPrefix8 = outputPrefix9 := by decide +kernel

def outputPrefix10Matrix : M := !![ofCode 4, ofCode 4, ofCode 6, ofCode 1; ofCode 5, ofCode 0, ofCode 7, ofCode 1; ofCode 6, ofCode 4, ofCode 5, ofCode 7; ofCode 6, ofCode 3, ofCode 7, ofCode 3]
def outputPrefix10Inverse : M := !![ofCode 3, ofCode 7, ofCode 1, ofCode 1; ofCode 7, ofCode 5, ofCode 7, ofCode 6; ofCode 3, ofCode 4, ofCode 0, ofCode 4; ofCode 6, ofCode 6, ofCode 5, ofCode 4]
theorem outputPrefix10_mul_inverse : outputPrefix10Matrix * outputPrefix10Inverse = 1 := by decide +kernel
theorem outputPrefix10_inverse_mul : outputPrefix10Inverse * outputPrefix10Matrix = 1 := by decide +kernel
def outputPrefix10 : UnitMatrix := ⟨outputPrefix10Matrix, outputPrefix10Inverse, outputPrefix10_mul_inverse, outputPrefix10_inverse_mul⟩

private theorem outputStep10 : cAut outputPrefix9 = outputPrefix10 := by decide +kernel

def outputPrefix11Matrix : M := !![ofCode 7, ofCode 1, ofCode 0, ofCode 3; ofCode 5, ofCode 0, ofCode 4, ofCode 0; ofCode 5, ofCode 5, ofCode 0, ofCode 6; ofCode 3, ofCode 6, ofCode 3, ofCode 1]
def outputPrefix11Inverse : M := !![ofCode 1, ofCode 6, ofCode 0, ofCode 3; ofCode 3, ofCode 0, ofCode 4, ofCode 0; ofCode 6, ofCode 5, ofCode 0, ofCode 1; ofCode 3, ofCode 5, ofCode 5, ofCode 7]
theorem outputPrefix11_mul_inverse : outputPrefix11Matrix * outputPrefix11Inverse = 1 := by decide +kernel
theorem outputPrefix11_inverse_mul : outputPrefix11Inverse * outputPrefix11Matrix = 1 := by decide +kernel
def outputPrefix11 : UnitMatrix := ⟨outputPrefix11Matrix, outputPrefix11Inverse, outputPrefix11_mul_inverse, outputPrefix11_inverse_mul⟩

private theorem outputStep11 : outerAut outputPrefix10 = outputPrefix11 := by decide +kernel

def outputPrefix12Matrix : M := !![ofCode 1, ofCode 3, ofCode 6, ofCode 3; ofCode 6, ofCode 0, ofCode 5, ofCode 5; ofCode 0, ofCode 4, ofCode 0, ofCode 5; ofCode 3, ofCode 0, ofCode 1, ofCode 7]
def outputPrefix12Inverse : M := !![ofCode 7, ofCode 5, ofCode 5, ofCode 3; ofCode 1, ofCode 0, ofCode 5, ofCode 6; ofCode 0, ofCode 4, ofCode 0, ofCode 3; ofCode 3, ofCode 0, ofCode 6, ofCode 1]
theorem outputPrefix12_mul_inverse : outputPrefix12Matrix * outputPrefix12Inverse = 1 := by decide +kernel
theorem outputPrefix12_inverse_mul : outputPrefix12Inverse * outputPrefix12Matrix = 1 := by decide +kernel
def outputPrefix12 : UnitMatrix := ⟨outputPrefix12Matrix, outputPrefix12Inverse, outputPrefix12_mul_inverse, outputPrefix12_inverse_mul⟩

private theorem outputStep12 : cAut outputPrefix11 = outputPrefix12 := by decide +kernel

def outputPrefix13Matrix : M := !![ofCode 1, ofCode 2, ofCode 1, ofCode 6; ofCode 6, ofCode 6, ofCode 0, ofCode 4; ofCode 7, ofCode 1, ofCode 3, ofCode 3; ofCode 2, ofCode 6, ofCode 3, ofCode 6]
def outputPrefix13Inverse : M := !![ofCode 6, ofCode 3, ofCode 4, ofCode 6; ofCode 3, ofCode 3, ofCode 0, ofCode 1; ofCode 6, ofCode 1, ofCode 6, ofCode 2; ofCode 2, ofCode 7, ofCode 6, ofCode 1]
theorem outputPrefix13_mul_inverse : outputPrefix13Matrix * outputPrefix13Inverse = 1 := by decide +kernel
theorem outputPrefix13_inverse_mul : outputPrefix13Inverse * outputPrefix13Matrix = 1 := by decide +kernel
def outputPrefix13 : UnitMatrix := ⟨outputPrefix13Matrix, outputPrefix13Inverse, outputPrefix13_mul_inverse, outputPrefix13_inverse_mul⟩

private theorem outputStep13 : outerAut.symm outputPrefix12 = outputPrefix13 := by decide +kernel

def outputPrefix14Matrix : M := !![ofCode 6, ofCode 3, ofCode 6, ofCode 2; ofCode 3, ofCode 3, ofCode 1, ofCode 7; ofCode 4, ofCode 0, ofCode 6, ofCode 6; ofCode 6, ofCode 1, ofCode 2, ofCode 1]
def outputPrefix14Inverse : M := !![ofCode 1, ofCode 6, ofCode 7, ofCode 2; ofCode 2, ofCode 6, ofCode 1, ofCode 6; ofCode 1, ofCode 0, ofCode 3, ofCode 3; ofCode 6, ofCode 4, ofCode 3, ofCode 6]
theorem outputPrefix14_mul_inverse : outputPrefix14Matrix * outputPrefix14Inverse = 1 := by decide +kernel
theorem outputPrefix14_inverse_mul : outputPrefix14Inverse * outputPrefix14Matrix = 1 := by decide +kernel
def outputPrefix14 : UnitMatrix := ⟨outputPrefix14Matrix, outputPrefix14Inverse, outputPrefix14_mul_inverse, outputPrefix14_inverse_mul⟩

private theorem outputStep14 : cAut outputPrefix13 = outputPrefix14 := by decide +kernel

def outputPrefix15Matrix : M := !![ofCode 2, ofCode 7, ofCode 1, ofCode 6; ofCode 2, ofCode 4, ofCode 6, ofCode 6; ofCode 5, ofCode 0, ofCode 6, ofCode 6; ofCode 6, ofCode 3, ofCode 1, ofCode 6]
def outputPrefix15Inverse : M := !![ofCode 6, ofCode 6, ofCode 6, ofCode 6; ofCode 1, ofCode 6, ofCode 6, ofCode 1; ofCode 3, ofCode 0, ofCode 4, ofCode 7; ofCode 6, ofCode 5, ofCode 2, ofCode 2]
theorem outputPrefix15_mul_inverse : outputPrefix15Matrix * outputPrefix15Inverse = 1 := by decide +kernel
theorem outputPrefix15_inverse_mul : outputPrefix15Inverse * outputPrefix15Matrix = 1 := by decide +kernel
def outputPrefix15 : UnitMatrix := ⟨outputPrefix15Matrix, outputPrefix15Inverse, outputPrefix15_mul_inverse, outputPrefix15_inverse_mul⟩

private theorem outputStep15 : outerAut outputPrefix14 = outputPrefix15 := by decide +kernel

def outputPrefix16Matrix : M := !![ofCode 6, ofCode 1, ofCode 3, ofCode 6; ofCode 6, ofCode 6, ofCode 0, ofCode 5; ofCode 6, ofCode 6, ofCode 4, ofCode 2; ofCode 6, ofCode 1, ofCode 7, ofCode 2]
def outputPrefix16Inverse : M := !![ofCode 2, ofCode 2, ofCode 5, ofCode 6; ofCode 7, ofCode 4, ofCode 0, ofCode 3; ofCode 1, ofCode 6, ofCode 6, ofCode 1; ofCode 6, ofCode 6, ofCode 6, ofCode 6]
theorem outputPrefix16_mul_inverse : outputPrefix16Matrix * outputPrefix16Inverse = 1 := by decide +kernel
theorem outputPrefix16_inverse_mul : outputPrefix16Inverse * outputPrefix16Matrix = 1 := by decide +kernel
def outputPrefix16 : UnitMatrix := ⟨outputPrefix16Matrix, outputPrefix16Inverse, outputPrefix16_mul_inverse, outputPrefix16_inverse_mul⟩

private theorem outputStep16 : cAut outputPrefix15 = outputPrefix16 := by decide +kernel

private theorem outputStep17 : outerAut outputPrefix16 = k := by decide +kernel

def outputAut : MulAut UnitMatrix := (((((((((((((((((cAut).trans outerAut.symm).trans cAut).trans outerAut.symm).trans cAut).trans outerAut).trans cAut).trans outerAut.symm).trans cAut).trans outerAut.symm).trans cAut).trans outerAut).trans cAut).trans outerAut.symm).trans cAut).trans outerAut).trans cAut).trans outerAut

theorem outputAut_x : outputAut x = k := by
  change outerAut (cAut (outerAut (cAut (outerAut.symm (cAut (outerAut (cAut (outerAut.symm (cAut (outerAut.symm (cAut (outerAut (cAut (outerAut.symm (cAut (outerAut.symm (cAut (x)))))))))))))))))) = k
  rw [outputStep0, outputStep1, outputStep2, outputStep3, outputStep4, outputStep5, outputStep6, outputStep7, outputStep8, outputStep9, outputStep10, outputStep11, outputStep12, outputStep13, outputStep14, outputStep15, outputStep16, outputStep17]

end Kourovka2135.SuzukiEightCoverCodeGoodWords
