import Kourovka2135.SLTwoGeneralLinearConjugation
import Kourovka2135.OddSLTwoCenter
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.LinearCombination

/-! Regular same-trace conjugacy in actual SL2 over an odd finite field.

The determinant of a GL2 intertwiner is corrected by a commuting matrix
aI+bM. Its determinant is the nondegenerate binary form a²+tr(M)ab+b².
The finite-field quadratic-sum pigeonhole theorem proves this form represents
every scalar when tr(M)²≠4. No split/nonsplit torus classification is needed.
-/

set_option autoImplicit false
noncomputable section
namespace Kourovka2135.SLTwoRegularTraceConjugacy

open scoped Matrix Polynomial
open Matrix Polynomial

variable {F : Type*} [Field F]

theorem exists_weighted_sum_squares [Finite F] (hodd : Odd (Nat.card F))
    (c : F) (hc : c ≠ 0) (d : F) :
    ∃ x y : F, x ^ 2 + c * y ^ 2 = d := by
  let : Fintype F := Fintype.ofFinite F
  let f : F[X] := X ^ 2
  let g : F[X] := C c * X ^ 2 - C d
  have hf : f.degree = 2 := degree_X_pow 2
  have hg : g.degree = 2 := by
    apply (degree_sub_eq_left_of_degree_lt ?_).trans (degree_C_mul_X_pow 2 hc)
    rw [degree_C_mul_X_pow 2 hc]
    exact lt_of_le_of_lt degree_C_le (by norm_num)
  have hcard : Fintype.card F % 2 = 1 := by
    simpa only [Nat.card_eq_fintype_card] using Nat.odd_iff.mp hodd
  obtain ⟨x, y, hxy⟩ := FiniteField.exists_root_sum_quadratic hf hg hcard
  refine ⟨x, y, ?_⟩
  have he : x ^ 2 + (c * y ^ 2 - d) = 0 := by
    simpa only [f, g, eval_pow, eval_X, eval_sub, eval_mul, eval_C] using hxy
  linear_combination he

theorem exists_binary_form_value [Finite F] (hodd : Odd (Nat.card F))
    (t : F) (ht : t ^ 2 ≠ 4) (d : F) :
    ∃ a b : F, a ^ 2 + t * a * b + b ^ 2 = d := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero (OddSLTwoCenter.ringChar_ne_two F hodd)
  have hc : (4 : F) - t ^ 2 ≠ 0 := sub_ne_zero.mpr ht.symm
  obtain ⟨x, y, hxy⟩ := exists_weighted_sum_squares hodd (4 - t ^ 2) hc (4 * d)
  let a : F := (x - t * y) / 2
  refine ⟨a, y, ?_⟩
  apply mul_left_cancel₀ (pow_ne_zero 2 h2)
  calc
    (2 : F) ^ 2 * (a ^ 2 + t * a * y + y ^ 2) =
        x ^ 2 + (4 - t ^ 2) * y ^ 2 := by
      dsimp only [a]
      field_simp [h2]
      ring
    _ = 4 * d := hxy
    _ = (2 : F) ^ 2 * d := by ring

def linearCombination (M : Matrix (Fin 2) (Fin 2) F) (a b : F) :
    Matrix (Fin 2) (Fin 2) F := Matrix.scalar (Fin 2) a + b • M

theorem linearCombination_det (M : Matrix (Fin 2) (Fin 2) F) (a b : F) :
    (linearCombination M a b).det = a ^ 2 + M.trace * a * b + M.det * b ^ 2 := by
  simp [linearCombination, Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.scalar]
  ring

theorem linearCombination_commutes (M : Matrix (Fin 2) (Fin 2) F) (a b : F) :
    linearCombination M a b * M = M * linearCombination M a b := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [linearCombination, Matrix.scalar, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- The determinant map on the actual GL2 centralizer is surjective onto
all nonzero scalars for a regular determinant-one matrix. -/
theorem exists_commuting_det [Finite F] (hodd : Odd (Nat.card F))
    (g : SLTwo.SL2 F) (hreg : g.val.trace ^ 2 ≠ 4)
    (d : F) (hd : d ≠ 0) :
    ∃ T : Matrix.GeneralLinearGroup (Fin 2) F,
      (T : Matrix (Fin 2) (Fin 2) F).det = d ∧
      (T : Matrix (Fin 2) (Fin 2) F) * g.val =
        g.val * (T : Matrix (Fin 2) (Fin 2) F) := by
  obtain ⟨a, b, hab⟩ := exists_binary_form_value hodd g.val.trace hreg d
  have hdet : (linearCombination g.val a b).det = d := by
    rw [linearCombination_det, g.prop, one_mul]
    exact hab
  let T := Matrix.GeneralLinearGroup.mkOfDetNeZero (linearCombination g.val a b)
    (by simpa only [hdet] using hd)
  exact ⟨T, hdet, linearCombination_commutes g.val a b⟩

theorem nonscalar_of_regular (g : SLTwo.SL2 F) (hreg : g.val.trace ^ 2 ≠ 4) :
    ¬ ∃ r : F, g.val = Matrix.scalar (Fin 2) r := by
  rintro ⟨r, hr⟩
  have hd : r ^ 2 = 1 := by
    simpa [hr, Matrix.det_fin_two, pow_two] using g.prop
  have ht : g.val.trace = 2 * r := by
    simp [hr, two_mul]
  apply hreg
  rw [ht]
  linear_combination (4 : F) * hd

/-- Same trace gives conjugacy by an actual determinant-one matrix, not
merely an automorphism induced by GL2. -/
theorem exists_conjugator [Finite F] (hodd : Odd (Nat.card F))
    (g h : SLTwo.SL2 F) (htrace : g.val.trace = h.val.trace)
    (hreg : g.val.trace ^ 2 ≠ 4) :
    ∃ S : SLTwo.SL2 F, S * g * S⁻¹ = h := by
  have hreg' : h.val.trace ^ 2 ≠ 4 := by rwa [← htrace]
  obtain ⟨C, hC⟩ := MatrixTwoSameTraceConjugacy.exists_conjugator g.val h.val
    (nonscalar_of_regular g hreg) (nonscalar_of_regular h hreg') htrace
    (g.prop.trans h.prop.symm)
  have hc : (C : Matrix (Fin 2) (Fin 2) F).det ≠ 0 :=
    Matrix.GeneralLinearGroup.det_ne_zero C
  obtain ⟨T, hT, hcomm⟩ := exists_commuting_det hodd g hreg
    (C : Matrix (Fin 2) (Fin 2) F).det⁻¹ (inv_ne_zero hc)
  let S : SLTwo.SL2 F :=
    ⟨(C : Matrix (Fin 2) (Fin 2) F) * (T : Matrix (Fin 2) (Fin 2) F), by
      rw [Matrix.det_mul, hT, mul_inv_cancel₀ hc]⟩
  have hCg : (C : Matrix (Fin 2) (Fin 2) F) * g.val =
      h.val * (C : Matrix (Fin 2) (Fin 2) F) := by
    have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) F =>
      M * (C : Matrix (Fin 2) (Fin 2) F)) hC
    simpa only [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one] using he
  have he : S * g = h * S := by
    apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_mul]
    change ((C : Matrix (Fin 2) (Fin 2) F) * (T : Matrix (Fin 2) (Fin 2) F)) * g.val =
      h.val * ((C : Matrix (Fin 2) (Fin 2) F) * (T : Matrix (Fin 2) (Fin 2) F))
    calc
      ((C : Matrix (Fin 2) (Fin 2) F) * (T : Matrix (Fin 2) (Fin 2) F)) * g.val =
          (C : Matrix (Fin 2) (Fin 2) F) * ((T : Matrix (Fin 2) (Fin 2) F) * g.val) :=
        Matrix.mul_assoc _ _ _
      _ = (C : Matrix (Fin 2) (Fin 2) F) * (g.val * (T : Matrix (Fin 2) (Fin 2) F)) :=
        by rw [hcomm]
      _ = ((C : Matrix (Fin 2) (Fin 2) F) * g.val) * (T : Matrix (Fin 2) (Fin 2) F) :=
        (Matrix.mul_assoc _ _ _).symm
      _ = (h.val * (C : Matrix (Fin 2) (Fin 2) F)) * (T : Matrix (Fin 2) (Fin 2) F) :=
        by rw [hCg]
      _ = h.val * ((C : Matrix (Fin 2) (Fin 2) F) * (T : Matrix (Fin 2) (Fin 2) F)) :=
        Matrix.mul_assoc _ _ _
  exact ⟨S, mul_inv_eq_iff_eq_mul.mpr he⟩

theorem isConj_of_trace [Finite F] (hodd : Odd (Nat.card F))
    (g h : SLTwo.SL2 F) (htrace : g.val.trace = h.val.trace)
    (hreg : g.val.trace ^ 2 ≠ 4) : IsConj g h :=
  isConj_iff.mpr (exists_conjugator hodd g h htrace hreg)

end Kourovka2135.SLTwoRegularTraceConjugacy
