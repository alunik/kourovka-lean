import Kourovka.Problem2153.WilsonModel.Sparse
import Kourovka.Problem2153.Simplicity.Scalar

set_option autoImplicit false

namespace Kourovka.Problem2153.WilsonModel.Frame

open Field8 Matrix

universe u v

/-- Row-form projective-frame argument, with an explicit two-sided inverse certificate. -/
theorem scalar_of_row_frame {K : Type u} [Field K] {n : Type v} [Fintype n] [DecidableEq n]
    (V Vinv A : Matrix n n K) (c : n → K)
    (hRight : V * Vinv = 1) (hLeft : Vinv * V = 1)
    (hc : ∀ i, c i ≠ 0)
    (hFrame : ∀ i, ∃ a : K, vecMul (V i) A = a • V i)
    (hBridge : ∃ μ : K, vecMul (vecMul c V) A = μ • vecMul c V) :
    ∃ μ : K, A = μ • (1 : Matrix n n K) := by
  classical
  choose a ha using hFrame
  obtain ⟨μ, hμ⟩ := hBridge
  have hVA : V * A = diagonal a * V := by
    ext i j
    have hi := congrFun (ha i) j
    simpa only [← mul_apply_eq_vecMul, Pi.smul_apply, smul_eq_mul, diagonal_mul] using hi
  have hDiag : V * A * Vinv = diagonal a := by
    rw [hVA, mul_assoc, hRight, mul_one]
  have hCoeff : vecMul c (diagonal a) = μ • c := by
    rw [← hDiag, ← vecMul_vecMul, ← vecMul_vecMul, hμ,
      smul_vecMul, vecMul_vecMul, hRight, vecMul_one]
  have haμ : ∀ i, a i = μ := by
    intro i
    have hi := congrFun hCoeff i
    simp only [vecMul_diagonal, Pi.smul_apply, smul_eq_mul] at hi
    exact mul_left_cancel₀ (hc i) (hi.trans (mul_comm μ (c i)))
  have hVA' : V * A = μ • V := by
    rw [hVA]
    ext i j
    simp only [diagonal_mul, haμ, Matrix.smul_apply, smul_eq_mul]
  refine ⟨μ, ?_⟩
  have hh := congrArg (fun M => Vinv * M) hVA'
  simpa only [← mul_assoc, hLeft, one_mul, Matrix.mul_smul] using hh

/-- Sparse columns evaluate a row-vector action without summing zero entries. -/
def sparseRowAction {n : Type*} (cols : Sparse.Table n) (v : n → F8) : n → F8 :=
  fun j => Sparse.rowDot (cols j) v

theorem sparseRowAction_eq {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n F8) (cols : Sparse.Table n) (hM : M.transpose = Sparse.eval cols)
    (v : n → F8) : vecMul v M = sparseRowAction cols v := by
  ext j
  have hj : (fun k => M k j) = fun k => Sparse.rowEval (cols j) k := by
    funext k
    exact congrFun (congrFun hM j) k
  change (∑ k, v k * M k j) = Sparse.rowDot (cols j) v
  calc (∑ k, v k * M k j) = ∑ k, Sparse.rowEval (cols j) k * v k := by
         apply Finset.sum_congr rfl
         intro k _
         rw [← congrFun hj k, mul_comm]
       _ = Sparse.rowDot (cols j) v := Sparse.rowEval_dot _ _

#print axioms scalar_of_row_frame
#print axioms sparseRowAction_eq

end Kourovka.Problem2153.WilsonModel.Frame
