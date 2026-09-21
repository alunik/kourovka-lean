import Kourovka2135.SuzukiEightCodeGeometry
import Kourovka2135.SuzukiTensorNatural

/-! The tiny natural-matrix coefficients used in the C2/C4 tensor norm proof.
The only finite check is a coefficient of three powers of the actual code root.
Field embeddings transport it to every natural Frobenius twist. -/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.SuzukiEightNormCoefficients

open SuzukiEightCodeField SuzukiEightCodeGeometry SuzukiTensorNatural SuzukiTorusMovingRank
open BenderSuzuki.MatrixGroups

/-- The canonical root matrix in the computable field. -/
def codeRoot : Matrix (Fin 4) (Fin 4) Element := rootMatrix alpha 0

theorem codeRoot_power_corner (j : Fin 3) :
    (codeRoot ^ (j.val + 1)) 0 3 = alpha ^ 6 := by
  fin_cases j <;> decide +kernel

variable (k : Type) [Field k] [CharP k 2] (σ : K 1 →+* k) (n : ℕ)

def coefficientEmbedding : Element →+* k :=
  (twistEmbedding k 1 σ n).comp actualEquiv.toRingHom

def corner : k := coefficientEmbedding k σ n (alpha ^ 6)

theorem corner_ne_zero : corner k σ n ≠ 0 := by
  exact (map_ne_zero (coefficientEmbedding k σ n)).mpr (pow_ne_zero 6 alpha_ne_zero)

theorem naturalTwist_B_matrix :
    LinearMap.toMatrixAlgEquiv' (naturalTwist k 1 σ n B) =
      (coefficientEmbedding k σ n).mapMatrix codeRoot := by
  change LinearMap.toMatrixAlgEquiv'
      (Matrix.toLinAlgEquiv' ((SuzukiRootMatrix 1 actualAlpha 0).map
        (twistEmbedding k 1 σ n))) = _
  rw [LinearMap.toMatrixAlgEquiv'_toLinAlgEquiv']
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [codeRoot, rootMatrix, SuzukiRootMatrix, coefficientEmbedding, actualAlpha]

/-- The same nonzero corner occurs in all three nonidentity powers. -/
theorem naturalTwist_B_corner (j : Fin 3) :
    ((naturalTwist k 1 σ n B) ^ (j.val + 1)) (Pi.single 3 1) 0 = corner k σ n := by
  have h : LinearMap.toMatrixAlgEquiv'
      ((naturalTwist k 1 σ n B) ^ (j.val + 1)) =
      (coefficientEmbedding k σ n).mapMatrix (codeRoot ^ (j.val + 1)) := by
    rw [map_pow, naturalTwist_B_matrix, map_pow]
  have he := congrArg (fun M : Matrix (Fin 4) (Fin 4) k => M 0 3) h
  change ((naturalTwist k 1 σ n B) ^ (j.val + 1)) (Pi.single 3 1) 0 =
    coefficientEmbedding k σ n ((codeRoot ^ (j.val + 1)) 0 3) at he
  rw [codeRoot_power_corner] at he
  exact he

/-- Weyl sends the first two basis vectors outside the first two coordinates. -/
theorem naturalTwist_C_top (i j : Fin 2) :
    naturalTwist k 1 σ n C (Pi.single (j.castAdd 2) 1) (i.castAdd 2) = 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [naturalTwist_apply, matrixHom, C, actualC, SuzukiWeylGL,
      SuzukiWeylMatrix, Pi.single_apply]

end Kourovka2135.SuzukiEightNormCoefficients
