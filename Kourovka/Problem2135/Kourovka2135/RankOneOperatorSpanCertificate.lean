import Kourovka2135.RepresentationDensityBaseChange
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.Matrix.Basis

/-! One actual rank-one operator and two cyclic bases certify full operator image.

The input rank-one operator belongs to the actual algebra image. Its left and
right translates form two explicitly invertible coordinate matrices. Their
sandwiches then span all matrices by an actual algebra-element construction.
No matrix-algebra dimension, numerical rank or irreducibility premise is used.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.RankOneOperatorSpanCertificate

variable {k n : Type*} [Field k] [Fintype n] [DecidableEq n]

/-- Columns of the chosen translates of the rank-one column vector. -/
def cyclicColumns (A : n → Matrix n n k) (v : n → k) : Matrix n n k :=
  fun i j => (A j).mulVec v i

/-- Rows of the chosen translates of the rank-one row vector. -/
def cyclicRows (B : n → Matrix n n k) (w : n → k) : Matrix n n k :=
  fun i j => Matrix.vecMul w (B i) j

omit [DecidableEq n] in
/-- The elementary outer-product expansion with the exact coefficient orientation. -/
theorem sum_outer_products (U D V : Matrix n n k) :
    (∑ i, ∑ j, D i j • Matrix.vecMulVec (fun a => U a i) (V j)) = U * D * V := by
  ext a b
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
    smul_eq_mul, Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ac_rfl

section Algebra

variable {R : Type*} [Ring R] [Algebra k R]

/-- An actual algebra map containing one rank-one element and two certified
cyclic bases is onto the full matrix algebra. -/
theorem algebraHom_surjective
    (f : R →ₐ[k] Matrix n n k) (r : R) (a b : n → R) (v w : n → k)
    (Uinv Vinv : Matrix n n k)
    (hr : f r = Matrix.vecMulVec v w)
    (hU : cyclicColumns (fun i => f (a i)) v * Uinv = 1)
    (hV : Vinv * cyclicRows (fun i => f (b i)) w = 1) :
    Function.Surjective f := by
  classical
  intro T
  let U := cyclicColumns (fun i => f (a i)) v
  let V := cyclicRows (fun i => f (b i)) w
  let D := Uinv * T * Vinv
  have hsandwich (i j : n) :
      f (a i * r * b j) = Matrix.vecMulVec (fun x => U x i) (V j) := by
    simp only [map_mul, hr, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul,
      U, V, cyclicColumns]
    rfl
  refine ⟨∑ i, ∑ j, D i j • (a i * r * b j), ?_⟩
  simp only [map_sum, map_smul, hsandwich]
  rw [sum_outer_products]
  calc
    U * D * V = (U * Uinv) * T * (Vinv * V) := by simp only [D, mul_assoc]
    _ = T := by rw [hU, hV, one_mul, mul_one]

end Algebra

section Representation

open scoped MonoidAlgebra
variable {G : Type*} [Monoid G]

/-- Actual matrix coordinates of the group-algebra action. -/
def matrixAction (ρ : Representation k G (n → k)) : k[G] →ₐ[k] Matrix n n k :=
  LinearMap.toMatrixAlgEquiv'.toAlgHom.comp ρ.asAlgebraHom

@[simp]
theorem matrixAction_apply (ρ : Representation k G (n → k)) (r : k[G]) :
    matrixAction ρ r = LinearMap.toMatrix' (ρ.asAlgebraHom r) := rfl

@[simp]
theorem matrixAction_single_one (ρ : Representation k G (n → k)) (g : G) :
    matrixAction ρ (MonoidAlgebra.single g 1) = LinearMap.toMatrix' (ρ g) := by
  rw [matrixAction_apply, Representation.asAlgebraHom_single_one]

/-- The representation form of the certificate uses genuine group elements
and an explicitly constructed element of their group algebra. -/
theorem asAlgebraHom_surjective
    (ρ : Representation k G (n → k)) (r : k[G]) (a b : n → G) (v w : n → k)
    (Uinv Vinv : Matrix n n k)
    (hr : LinearMap.toMatrix' (ρ.asAlgebraHom r) = Matrix.vecMulVec v w)
    (hU : cyclicColumns (fun i => LinearMap.toMatrix' (ρ (a i))) v * Uinv = 1)
    (hV : Vinv * cyclicRows (fun i => LinearMap.toMatrix' (ρ (b i))) w = 1) :
    Function.Surjective ρ.asAlgebraHom := by
  have hsurj : Function.Surjective (matrixAction ρ) := by
    apply algebraHom_surjective (matrixAction ρ) r
      (fun i => MonoidAlgebra.single (a i) 1)
      (fun i => MonoidAlgebra.single (b i) 1) v w Uinv Vinv hr
    · simpa only [matrixAction_single_one] using hU
    · simpa only [matrixAction_single_one] using hV
  intro T
  obtain ⟨x, hx⟩ := hsurj (LinearMap.toMatrix' T)
  exact ⟨x, LinearMap.toMatrix'.injective hx⟩

end Representation

end Kourovka2135.RankOneOperatorSpanCertificate
