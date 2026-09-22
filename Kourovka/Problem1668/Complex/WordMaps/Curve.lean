import WordMaps.Polynomial
import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.Trace

set_option autoImplicit false

open Polynomial
open scoped MatrixGroups

namespace WordMaps

variable {K : Type*} [Field K]

/-- Evaluate a determinant-one polynomial matrix. -/
noncomputable def evalSL (t : K) : SL(2, K[X]) →* SL(2, K) :=
  Matrix.SpecialLinearGroup.map (Polynomial.evalRingHom t)

@[simp] theorem evalSL_entry (t : K) (M : SL(2, K[X])) (i j : Fin 2) :
    evalSL t M i j = (M i j).eval t := rfl

@[simp] theorem trace_evalSL (t : K) (M : SL(2, K[X])) :
    Matrix.trace (evalSL t M).val = (Matrix.trace M.val).eval t := by
  simp only [Matrix.trace_fin_two, eval_add]
  rfl

/-- The trace has zero derivative at a scalar point of a determinant-one curve. -/
theorem trace_derivative_zero_at_scalar (a b c d : K[X]) (t e : K)
    (he : e ≠ 0) (hdet : a * d - b * c = 1)
    (ha : a.eval t = e) (hb : b.eval t = 0)
    (hc : c.eval t = 0) (hd : d.eval t = e) :
    (a + d).derivative.eval t = 0 := by
  have h := congrArg (fun p : K[X] => p.derivative.eval t) hdet
  simp only [derivative_sub, derivative_mul, derivative_one, eval_sub,
    eval_add, eval_mul, eval_zero, ha, hb, hc, hd, mul_zero, zero_mul,
    add_zero, sub_zero] at h
  have hsum : a.derivative.eval t + d.derivative.eval t = 0 := by
    apply (mul_eq_zero.mp (show e *
      (a.derivative.eval t + d.derivative.eval t) = 0 by
        calc
          _ = a.derivative.eval t * e + e * d.derivative.eval t := by ring
          _ = 0 := h)).resolve_left he
  simpa only [derivative_add, eval_add] using hsum

theorem trace_derivative_zero_of_eval_central (t : K) (M : SL(2, K[X]))
    (hM : evalSL t M ∈ Subgroup.center SL(2, K)) :
    (Matrix.trace M.val).derivative.eval t = 0 := by
  obtain ⟨e, he, hscalar⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hM
  have hene : e ≠ 0 := by
    intro he0
    simp [he0] at he
  have h00 := congrArg (fun A : Matrix (Fin 2) (Fin 2) K => A 0 0) hscalar
  have h01 := congrArg (fun A : Matrix (Fin 2) (Fin 2) K => A 0 1) hscalar
  have h10 := congrArg (fun A : Matrix (Fin 2) (Fin 2) K => A 1 0) hscalar
  have h11 := congrArg (fun A : Matrix (Fin 2) (Fin 2) K => A 1 1) hscalar
  simp only [Matrix.scalar_apply, Matrix.diagonal_apply,
    Fin.isValue, one_ne_zero, zero_ne_one, evalSL_entry] at *
  rw [Matrix.trace_fin_two]
  exact trace_derivative_zero_at_scalar (M 0 0) (M 0 1) (M 1 0) (M 1 1) t e hene
    (by simpa only [Matrix.det_fin_two] using M.property)
    h00.symm h01.symm h10.symm h11.symm

/-- A nonconstant-trace polynomial curve meets a noncentral trace ±2 fibre. -/
theorem exists_noncentral_trace_two [CharZero K] [IsAlgClosed K]
    (M : SL(2, K[X])) (hM : (Matrix.trace M.val).natDegree ≠ 0) :
    ∃ t : K, (Matrix.trace (evalSL t M).val = 2 ∨
      Matrix.trace (evalSL t M).val = -2) ∧
      evalSL t M ∉ Subgroup.center SL(2, K) := by
  obtain ⟨t, ht, hd⟩ := exists_regular_fiber (Matrix.trace M.val) hM 2 (-2) (by norm_num)
  refine ⟨t, ?_, ?_⟩
  · simpa only [trace_evalSL] using ht
  · intro hc
    exact hd (trace_derivative_zero_of_eval_central t M hc)

end WordMaps
