import Kourovka2135.SuzukiBrandlMatrices
import Kourovka2135.DerivedCentralization

/-! An explicit upper triangular Brandl commutator, in the actual Suzuki
matrix convention. Its characteristic polynomial is that of the square
of the torus input. -/

set_option autoImplicit false
noncomputable section
namespace Kourovka2135.SuzukiBrandlCommutator

open Matrix Polynomial SuzukiBrandlMatrices SuzukiTorusMovingRank
open scoped Matrix MatrixGroups Polynomial
open BenderSuzuki.MatrixGroups

variable {F : Type*} [Field F] [CharP F 2]

def yInverse (b B : F) : Matrix (Fin 4) (Fin 4) F :=
  !![B, b, 0, 1; b, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0]

theorem yMatrix_mul_inverse (b B : F) : yMatrix b B * yInverse b B = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [yMatrix, yInverse, Matrix.mul_apply, Fin.sum_univ_four,
      CharTwo.add_self_eq_zero]

def diagonalPair (u v : F) : Matrix (Fin 4) (Fin 4) F :=
  Matrix.diagonal ![u, v, v⁻¹, u⁻¹]

def upperCommutator (u v b B : F) : Matrix (Fin 4) (Fin 4) F :=
  !![u⁻¹ ^ 2, 0, b * (v / u + u⁻¹ ^ 2), B * (1 + u⁻¹ ^ 2);
     0, v⁻¹ ^ 2, 0, b * (u / v + v⁻¹ ^ 2);
     0, 0, v ^ 2, 0;
     0, 0, 0, u ^ 2]

omit [CharP F 2] in
theorem commutator_formula (u v b B : F) (hu : u ≠ 0) (hv : v ≠ 0) :
    diagonalPair u⁻¹ v⁻¹ * yInverse b B * diagonalPair u v * yMatrix b B =
      upperCommutator u v b B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagonalPair, yMatrix, yInverse, upperCommutator,
      Matrix.mul_apply, Fin.sum_univ_four] <;>
    field_simp

omit [CharP F 2] in
theorem charpoly_upperCommutator (u v b B : F) :
    (upperCommutator u v b B).charpoly = (diagonalPair (u ^ 2) (v ^ 2)).charpoly := by
  have ht : (upperCommutator u v b B).IsUpperTriangular := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [upperCommutator] at hij ⊢
  rw [Matrix.charpoly_of_isUpperTriangular _ ht, diagonalPair, Matrix.charpoly_diagonal]
  simp [Fin.prod_univ_four, upperCommutator, inv_pow]
  ring

/-- The faithful actual matrix homomorphism. -/
def matrixHom (m : ℕ) : G m →* Matrix (Fin 4) (Fin 4) (K m) :=
  (Units.coeHom _).comp (SuzukiMatrixSubgroup m).subtype

theorem matrixHom_injective (m : ℕ) : Function.Injective (matrixHom m) :=
  Units.val_injective.comp Subtype.val_injective

theorem matrixHom_y (m : ℕ) (b : K m) :
    matrixHom m (y m b) = yMatrix b (tits m b) := y_coe m b

theorem matrixHom_y_inv (m : ℕ) (b : K m) :
    matrixHom m ((y m b)⁻¹) = yInverse b (tits m b) := by
  change ((((y m b).val)⁻¹ : GL (Fin 4) (K m)) : Matrix (Fin 4) (Fin 4) (K m)) = _
  apply Units.inv_eq_of_mul_eq_one_right
  rw [y_coe]
  exact yMatrix_mul_inverse b (tits m b)

/-- Change from the vendor unit parameter to the lambda parameter. -/
theorem matrixHom_torus (m : ℕ) (x : (K m)ˣ) :
    matrixHom m (torusHom m x) =
      diagonalPair ((x : K m) ^ (2 ^ m) * tits m ((x : K m) ^ (2 ^ m)))
        ((x : K m) ^ (2 ^ m)) := by
  rw [tits_middle]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixHom, torusHom, SuzukiTorusGL, SuzukiTorusMatrix,
      diagonalPair, pow_add, mul_comm]

theorem matrixHom_torus_inv (m : ℕ) (x : (K m)ˣ) :
    matrixHom m ((torusHom m x)⁻¹) =
      diagonalPair (((x : K m) ^ (2 ^ m) * tits m ((x : K m) ^ (2 ^ m)))⁻¹)
        (((x : K m) ^ (2 ^ m))⁻¹) := by
  rw [← map_inv, matrixHom_torus]
  simp only [Units.val_inv_eq_inv_val, inv_pow, map_inv₀, mul_inv]

theorem matrixHom_commutator (m : ℕ) (x : (K m)ˣ) (b : K m) :
    matrixHom m (paperCommutator (torusHom m x) (y m b)) =
      upperCommutator
        ((x : K m) ^ (2 ^ m) * tits m ((x : K m) ^ (2 ^ m)))
        ((x : K m) ^ (2 ^ m)) b (tits m b) := by
  simp only [paperCommutator, map_mul, matrixHom_torus_inv, matrixHom_y_inv,
    matrixHom_torus, matrixHom_y]
  apply commutator_formula
  · exact mul_ne_zero (pow_ne_zero _ x.ne_zero)
      ((map_ne_zero (tits m)).2 (pow_ne_zero _ x.ne_zero))
  · exact pow_ne_zero _ x.ne_zero

end Kourovka2135.SuzukiBrandlCommutator
