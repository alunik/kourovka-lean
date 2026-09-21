import Kourovka2135.SuzukiEightCoverCodeMatrices

/-! The actual semilinear lift of the order-three ATLAS normalizer.
Only generator images and finite field laws are certified here. -/
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
namespace Kourovka2135.SuzukiEightCoverSemilinear
open SuzukiEightCodeField SuzukiEightCoverCodeMatrices

def fieldAut : Element ≃+* Element where
  toFun a := a ^ 4
  invFun a := a ^ 2
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_mul' := by decide +kernel
  map_add' := by decide +kernel

def jMatrix : M := !![ofCode 7, ofCode 1, ofCode 1, ofCode 2; ofCode 2, ofCode 2, ofCode 1, ofCode 1; ofCode 4, ofCode 1, ofCode 1, ofCode 7; ofCode 2, ofCode 7, ofCode 6, ofCode 1]
def jInverse : M := !![ofCode 5, ofCode 6, ofCode 5, ofCode 1; ofCode 3, ofCode 5, ofCode 5, ofCode 5; ofCode 6, ofCode 5, ofCode 1, ofCode 5; ofCode 1, ofCode 2, ofCode 1, ofCode 6]
theorem j_mul_inverse : jMatrix * jInverse = 1 := by decide +kernel
theorem j_inverse_mul : jInverse * jMatrix = 1 := by decide +kernel
def j : UnitMatrix := ⟨jMatrix, jInverse, j_mul_inverse, j_inverse_mul⟩

def adMatrix : M := !![ofCode 2, ofCode 0, ofCode 1, ofCode 6; ofCode 3, ofCode 3, ofCode 4, ofCode 1; ofCode 1, ofCode 6, ofCode 3, ofCode 0; ofCode 7, ofCode 1, ofCode 3, ofCode 2]
def bdMatrix : M := !![ofCode 6, ofCode 0, ofCode 7, ofCode 2; ofCode 1, ofCode 7, ofCode 2, ofCode 3; ofCode 0, ofCode 3, ofCode 4, ofCode 6; ofCode 2, ofCode 5, ofCode 3, ofCode 5]
private def cFrob : M := !![ofCode 0, ofCode 0, ofCode 0, ofCode 1; ofCode 0, ofCode 0, ofCode 1, ofCode 0; ofCode 0, ofCode 1, ofCode 0, ofCode 0; ofCode 1, ofCode 0, ofCode 0, ofCode 0]
private theorem cfrob_eq : cMatrix.map fieldAut = cFrob := by decide +kernel
private def cMid : M := !![ofCode 1, ofCode 5, ofCode 6, ofCode 5; ofCode 5, ofCode 5, ofCode 5, ofCode 3; ofCode 5, ofCode 1, ofCode 5, ofCode 6; ofCode 6, ofCode 1, ofCode 2, ofCode 1]
private theorem cLeft : jInverse * cFrob = cMid := by decide +kernel
private theorem cRight : cMid * jMatrix = adMatrix := by decide +kernel
theorem c_semilinear : jInverse * (cMatrix.map fieldAut) * jMatrix = adMatrix := by
  rw [cfrob_eq, cLeft, cRight]

private def bFrob : M := !![ofCode 1, ofCode 7, ofCode 0, ofCode 4; ofCode 0, ofCode 1, ofCode 5, ofCode 6; ofCode 0, ofCode 0, ofCode 1, ofCode 7; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem bfrob_eq : bMatrix.map fieldAut = bFrob := by decide +kernel
private def bMid : M := !![ofCode 5, ofCode 0, ofCode 6, ofCode 7; ofCode 3, ofCode 7, ofCode 2, ofCode 7; ofCode 6, ofCode 1, ofCode 6, ofCode 4; ofCode 1, ofCode 5, ofCode 0, ofCode 2]
private theorem bLeft : jInverse * bFrob = bMid := by decide +kernel
private theorem bRight : bMid * jMatrix = bdMatrix := by decide +kernel
theorem b_semilinear : jInverse * (bMatrix.map fieldAut) * jMatrix = bdMatrix := by
  rw [bfrob_eq, bLeft, bRight]

def frobeniusGL : MulAut UnitMatrix := Units.mapEquiv (fieldAut.mapMatrix).toMulEquiv

def outerAut : MulAut UnitMatrix := frobeniusGL.trans (MulAut.conj j⁻¹)

@[simp] theorem outerAut_val (g : UnitMatrix) :
    (outerAut g).val = jInverse * (g.val.map fieldAut) * jMatrix := rfl

end Kourovka2135.SuzukiEightCoverSemilinear
