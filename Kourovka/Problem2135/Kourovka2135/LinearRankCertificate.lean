import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! Small inverse certificates give lower bounds on the range of a linear map.
The input is an actual operator identity; no matrix-rank computation or
external elimination routine is trusted. -/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.LinearRankCertificate

variable {k V W X : Type*} [Field k]
variable [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
variable [AddCommGroup X] [Module k X]

/-- A certified left inverse of a restriction injects its domain into the range. -/
theorem finrank_le_range [FiniteDimensional k W]
    (T : V →ₗ[k] W) (columns : X →ₗ[k] V) (rows : W →ₗ[k] X)
    (h : rows.comp (T.comp columns) = LinearMap.id) :
    Module.finrank k X ≤ Module.finrank k (LinearMap.range T) := by
  let f : X →ₗ[k] LinearMap.range T := T.rangeRestrict.comp columns
  apply LinearMap.finrank_le_finrank_of_injective (f := f)
  intro x y hxy
  have ht : T (columns x) = T (columns y) := congrArg Subtype.val hxy
  have hh := congrArg (fun A : X →ₗ[k] X => A x) h
  have hi := congrArg (fun A : X →ₗ[k] X => A y) h
  change rows (T (columns x)) = x at hh
  change rows (T (columns y)) = y at hi
  exact hh.symm.trans ((congrArg rows ht).trans hi)

/-- A square identity certificate of size r proves rank at least r. -/
theorem nat_le_range [FiniteDimensional k W] (r : ℕ)
    (T : V →ₗ[k] W) (columns : (Fin r → k) →ₗ[k] V)
    (rows : W →ₗ[k] (Fin r → k))
    (h : rows.comp (T.comp columns) = LinearMap.id) :
    r ≤ Module.finrank k (LinearMap.range T) := by
  simpa using finrank_le_range T columns rows h

/-- The matrix form of the certificate, suitable for ordinary finite `decide`. -/
theorem matrix_rank_lower_bound
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (r : ℕ) (T : Matrix m n k) (C : Matrix n (Fin r) k) (R : Matrix (Fin r) m k)
    (h : R * (T * C) = 1) :
    r ≤ Module.finrank k (LinearMap.range T.mulVecLin) := by
  apply nat_le_range r T.mulVecLin C.mulVecLin R.mulVecLin
  rw [← Matrix.mulVecLin_mul, ← Matrix.mulVecLin_mul, h, Matrix.mulVecLin_one]

end Kourovka2135.LinearRankCertificate
