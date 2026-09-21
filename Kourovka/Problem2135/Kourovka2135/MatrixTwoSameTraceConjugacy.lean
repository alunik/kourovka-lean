import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-! Two nonscalar two-by-two matrices over a field with the same trace and
determinant are conjugate by an actual invertible matrix. The proof constructs
a cyclic basis from one of the three vectors e1, e2, e1+e2. -/

set_option autoImplicit false
noncomputable section
namespace Kourovka2135.MatrixTwoSameTraceConjugacy
open scoped Matrix
open Matrix
variable {F : Type*} [Field F]

def cyclicBasis (M : Matrix (Fin 2) (Fin 2) F) (x y : F) :
    Matrix (Fin 2) (Fin 2) F :=
  !![x, M 0 0 * x + M 0 1 * y; y, M 1 0 * x + M 1 1 * y]

def companion (M : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 2) (Fin 2) F :=
  !![0, -M.det; 1, M.trace]

theorem cyclicBasis_relation (M : Matrix (Fin 2) (Fin 2) F) (x y : F) :
    M * cyclicBasis M x y = cyclicBasis M x y * companion M := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cyclicBasis, companion, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.det_fin_two, Matrix.trace_fin_two] <;> ring

theorem exists_cyclicBasis (M : Matrix (Fin 2) (Fin 2) F)
    (h : ¬ ∃ r : F, M = Matrix.scalar (Fin 2) r) :
    ∃ x y : F, (cyclicBasis M x y).det ≠ 0 := by
  by_cases hc : M 1 0 = 0
  · by_cases hb : M 0 1 = 0
    · have hd : M 1 1 - M 0 0 ≠ 0 := by
        intro he
        apply h
        refine ⟨M 0 0, ?_⟩
        have heq := sub_eq_zero.mp he
        ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.scalar, hb, hc, heq]
      refine ⟨1, 1, ?_⟩
      simpa [cyclicBasis, Matrix.det_fin_two_of, hb, hc] using hd
    · refine ⟨0, 1, ?_⟩
      simpa [cyclicBasis, Matrix.det_fin_two_of] using neg_ne_zero.mpr hb
  · refine ⟨1, 0, ?_⟩
    simpa [cyclicBasis, Matrix.det_fin_two_of] using hc

theorem exists_intertwiner (M : Matrix (Fin 2) (Fin 2) F)
    (h : ¬ ∃ r : F, M = Matrix.scalar (Fin 2) r) :
    ∃ C : Matrix.GeneralLinearGroup (Fin 2) F,
      M * (C : Matrix (Fin 2) (Fin 2) F) = (C : Matrix (Fin 2) (Fin 2) F) * companion M := by
  obtain ⟨x, y, hd⟩ := exists_cyclicBasis M h
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (cyclicBasis M x y) hd, ?_⟩
  exact cyclicBasis_relation M x y

theorem exists_conjugator (M N : Matrix (Fin 2) (Fin 2) F)
    (hM : ¬ ∃ r : F, M = Matrix.scalar (Fin 2) r)
    (hN : ¬ ∃ r : F, N = Matrix.scalar (Fin 2) r)
    (htrace : M.trace = N.trace) (hdet : M.det = N.det) :
    ∃ C : Matrix.GeneralLinearGroup (Fin 2) F,
      (C : Matrix (Fin 2) (Fin 2) F) * M *
        ((C⁻¹ : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = N := by
  obtain ⟨A, hA⟩ := exists_intertwiner M hM
  obtain ⟨B, hB⟩ := exists_intertwiner N hN
  have hc : companion M = companion N := by simp only [companion, htrace, hdet]
  have hi : (↑A⁻¹ : Matrix (Fin 2) (Fin 2) F) * M =
      companion M * (↑A⁻¹ : Matrix (Fin 2) (Fin 2) F) := by
    have ht := congrArg (fun X : Matrix (Fin 2) (Fin 2) F =>
      (↑A⁻¹ : Matrix (Fin 2) (Fin 2) F) * X * (↑A⁻¹ : Matrix (Fin 2) (Fin 2) F)) hA
    simpa only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul,
      Units.mul_inv_cancel_right] using ht
  refine ⟨B * A⁻¹, ?_⟩
  simp only [_root_.mul_inv_rev, inv_inv, Matrix.GeneralLinearGroup.coe_mul]
  calc
    (↑B * ↑A⁻¹) * M * (↑A * ↑B⁻¹) =
        ↑B * (↑A⁻¹ * M) * (↑A * ↑B⁻¹) := by simp only [Matrix.mul_assoc]
    _ = ↑B * (companion M * ↑A⁻¹) * (↑A * ↑B⁻¹) := by rw [hi]
    _ = (↑B * companion N) * ↑B⁻¹ := by simp [hc, Matrix.mul_assoc]
    _ = N := by rw [← hB]; simp [Matrix.mul_assoc]

end Kourovka2135.MatrixTwoSameTraceConjugacy
