import Kourovka2135.SuzukiTorusMovingRank
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Tactic

/-! Actual Suzuki Brandl matrices and elementary characteristic polynomials.
No conjugacy, generation, or representation classification is assumed. -/

set_option autoImplicit false
noncomputable section
namespace Kourovka2135.SuzukiBrandlMatrices

open Matrix Polynomial
open scoped Matrix MatrixGroups Polynomial
open BenderSuzuki.MatrixGroups
open SuzukiTorusMovingRank

variable {F : Type*} [Field F] [CharP F 2]

/-- The Weyl times central-root matrix in the upper-root convention. -/
def yMatrix (b B : F) : Matrix (Fin 4) (Fin 4) F :=
  !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, b; 1, 0, b, B]

theorem charpoly_yMatrix (b B : F) :
    (yMatrix b B).charpoly =
      X ^ 4 + C B * X ^ 3 + C (b ^ 2) * X ^ 2 + C B * X + 1 := by
  rw [Matrix.charpoly, Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_four, Matrix.det_fin_three, Matrix.charmatrix,
    yMatrix, Matrix.submatrix, Fin.succAbove, CharTwo.neg_eq, CharTwo.sub_eq_add]
  ring_nf
  have htwo : (2 : F[X]) = 0 := CharP.cast_eq_zero (F[X]) 2
  rw [htwo, mul_zero, add_zero]

/-- The actual group element, with generator membership displayed. -/
def y (m : ℕ) (b : K m) : G m :=
  ⟨SuzukiWeylGL m * SuzukiRootGL m 0 b,
    (SuzukiMatrixSubgroup m).mul_mem
      (Subgroup.subset_closure (Or.inr (Or.inr rfl)))
      (Subgroup.subset_closure (Or.inl ⟨0, b, rfl⟩))⟩

theorem y_coe (m : ℕ) (b : K m) :
    (((y m b).val : GL (Fin 4) (K m)) : Matrix (Fin 4) (Fin 4) (K m)) =
      yMatrix b (tits m b) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [y, yMatrix, SuzukiWeylGL, SuzukiWeylMatrix, SuzukiRootGL,
      SuzukiRootMatrix, Matrix.mul_apply, Fin.sum_univ_four, tits_apply]

theorem y_ne_one (m : ℕ) (b : K m) : y m b ≠ 1 := by
  intro h
  have he := congrArg (fun g : G m =>
    (((g.val : GL (Fin 4) (K m)) : Matrix (Fin 4) (Fin 4) (K m)) 0 3)) h
  simp [y_coe, yMatrix] at he

def traceParameter (σ : F ≃+* F) (a : F) : F :=
  a * σ a + a + a⁻¹ + (a * σ a)⁻¹

omit [CharP F 2] in
/-- The middle characteristic-polynomial coefficient is the Tits image
of the trace. This is a scalar identity using only σ²=Frobenius. -/
theorem middle_coefficient (σ : F ≃+* F) (hσ : ∀ x, σ (σ x) = x ^ 2)
    (a : F) (ha : a ≠ 0) :
    (a * σ a + (a * σ a)⁻¹) * (a + a⁻¹) = σ (traceParameter σ a) := by
  have hs : σ a ≠ 0 := (map_ne_zero σ).2 ha
  simp only [traceParameter, map_add, map_mul, map_inv₀, hσ]
  field_simp
  ring

/-- Four actual torus eigenvalues in the lambda convention. -/
def weights (σ : F ≃+* F) (a : F) : Fin 4 → F :=
  ![a * σ a, a, a⁻¹, (a * σ a)⁻¹]

theorem sq_eq_one_iff (a : F) : a ^ 2 = 1 ↔ a = 1 := by
  simpa only [one_pow, CharTwo.neg_eq, or_self] using
    (sq_eq_sq_iff_eq_or_eq_neg (a := a) (b := (1 : F)))

omit [CharP F 2] in
theorem norm_eq_one_iff (σ : F ≃+* F) (hσ : ∀ x, σ (σ x) = x ^ 2)
    (a : F) (ha : a ≠ 0) : a * σ a = 1 ↔ a = 1 := by
  constructor
  · intro hn
    have ht := congrArg σ hn
    simp only [map_mul, map_one, hσ] at ht
    have hs : σ a ≠ 0 := (map_ne_zero σ).2 ha
    have hh : a ^ 2 = a := by
      apply mul_left_cancel₀ hs
      exact ht.trans (by simpa [mul_comm] using hn.symm)
    apply mul_left_cancel₀ ha
    simpa [pow_two] using hh
  · rintro rfl
    simp

theorem second_norm_eq_one_iff (σ : F ≃+* F) (hσ : ∀ x, σ (σ x) = x ^ 2)
    (a : F) (ha : a ≠ 0) : a ^ 2 * σ a = 1 ↔ a = 1 := by
  constructor
  · intro hn
    have ht := congrArg σ hn
    simp only [map_mul, map_pow, map_one, hσ] at ht
    have hn' : (a * σ a) ^ 2 = 1 := by simpa [mul_pow, mul_comm] using ht
    exact (norm_eq_one_iff σ hσ a ha).mp ((sq_eq_one_iff _).mp hn')
  · rintro rfl
    simp

theorem weights_injective (σ : F ≃+* F) (hσ : ∀ x, σ (σ x) = x ^ 2)
    (a : F) (ha : a ≠ 0) (hne : a ≠ 1) : Function.Injective (weights σ a) := by
  have hs : σ a ≠ 0 := (map_ne_zero σ).2 ha
  have hn : a * σ a ≠ 1 := fun h => hne ((norm_eq_one_iff σ hσ a ha).mp h)
  have hn2 : a ^ 2 * σ a ≠ 1 := fun h =>
    hne ((second_norm_eq_one_iff σ hσ a ha).mp h)
  have hab : a * σ a ≠ a := by
    intro h
    have hh : σ a = 1 := (mul_left_cancel₀ ha) (h.trans (mul_one a).symm)
    apply hne
    apply σ.injective
    simpa using hh
  have hac : a * σ a ≠ a⁻¹ := by
    intro h
    apply hn2
    have hh := congrArg (fun t : F => a * t) h
    simpa [ha, ← mul_assoc, ← pow_two] using hh
  have had : a * σ a ≠ (a * σ a)⁻¹ := by
    intro h
    apply hn
    apply (sq_eq_one_iff _).mp
    calc
      (a * σ a) ^ 2 = (a * σ a) * (a * σ a)⁻¹ := by rw [pow_two, ← h]
      _ = 1 := mul_inv_cancel₀ (mul_ne_zero ha hs)
  have hbc : a ≠ a⁻¹ := by
    intro h
    apply hne
    apply (sq_eq_one_iff _).mp
    calc
      a ^ 2 = a * a⁻¹ := by rw [pow_two, ← h]
      _ = 1 := mul_inv_cancel₀ ha
  have hbd : a ≠ (a * σ a)⁻¹ := by
    intro h
    apply hac
    simpa only [inv_inv] using (congrArg Inv.inv h).symm
  have hcd : a⁻¹ ≠ (a * σ a)⁻¹ := by
    intro h
    apply hab
    exact (inv_inj.mp h).symm
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [weights, Ne.symm]

theorem reciprocal_pair (a : F) (ha : a ≠ 0) :
    (X - C a) * (X - C a⁻¹) =
      (X ^ 2 + C (a + a⁻¹) * X + 1 : F[X]) := by
  calc
    _ = X ^ 2 + (C a + C a⁻¹) * X + C a * C a⁻¹ := by
      simp only [CharTwo.sub_eq_add]
      ring
    _ = _ := by rw [← C_add, ← C_mul, mul_inv_cancel₀ ha, C_1]

theorem reciprocal_quartic (a b : F) :
    (X ^ 2 + C a * X + 1) * (X ^ 2 + C b * X + 1) =
      (X ^ 4 + C (a + b) * X ^ 3 + C (a * b) * X ^ 2 +
        C (a + b) * X + 1 : F[X]) := by
  simp only [C_add, C_mul]
  ring_nf
  have htwo : (2 : F[X]) = 0 := CharP.cast_eq_zero (F[X]) 2
  rw [htwo, mul_zero, add_zero]

theorem weights_polynomial (σ : F ≃+* F) (hσ : ∀ x, σ (σ x) = x ^ 2)
    (a : F) (ha : a ≠ 0) :
    (∏ i : Fin 4, (X - C (weights σ a i))) =
      X ^ 4 + C (traceParameter σ a) * X ^ 3 +
        C (σ (traceParameter σ a)) * X ^ 2 + C (traceParameter σ a) * X + 1 := by
  have hs : σ a ≠ 0 := (map_ne_zero σ).2 ha
  rw [Fin.prod_univ_four]
  change (X - C (a * σ a)) * (X - C a) * (X - C a⁻¹) *
      (X - C (a * σ a)⁻¹) = _
  rw [show (X - C (a * σ a)) * (X - C a) * (X - C a⁻¹) *
      (X - C (a * σ a)⁻¹) =
      ((X - C (a * σ a)) * (X - C (a * σ a)⁻¹)) *
        ((X - C a) * (X - C a⁻¹)) by ring]
  rw [reciprocal_pair _ (mul_ne_zero ha hs), reciprocal_pair a ha,
    reciprocal_quartic, middle_coefficient σ hσ a ha]
  have ht : a * σ a + (a * σ a)⁻¹ + (a + a⁻¹) = traceParameter σ a := by
    dsimp [traceParameter]
    ring
  rw [ht]

/-- The Brandl parameter gives exactly the split torus characteristic polynomial. -/
theorem charpoly_yMatrix_parameter (σ : F ≃+* F)
    (hσ : ∀ x, σ (σ x) = x ^ 2) (a : F) (ha : a ≠ 0) :
    (yMatrix (σ.symm (traceParameter σ a)) (traceParameter σ a)).charpoly =
      ∏ i : Fin 4, (X - C (weights σ a i)) := by
  have hb : (σ.symm (traceParameter σ a)) ^ 2 = σ (traceParameter σ a) := by
    rw [← hσ, σ.apply_symm_apply]
  rw [charpoly_yMatrix, hb, weights_polynomial σ hσ a ha]

/-- A matrix with these four distinct rth roots as characteristic roots
has actual rth power one, by Cayley-Hamilton. -/
theorem pow_eq_one_of_charpoly_weights (σ : F ≃+* F)
    (hσ : ∀ x, σ (σ x) = x ^ 2) (a : F) (ha : a ≠ 0) (hne : a ≠ 1)
    (r : ℕ) (har : a ^ r = 1) (M : Matrix (Fin 4) (Fin 4) F)
    (hc : M.charpoly = ∏ i : Fin 4, (X - C (weights σ a i))) : M ^ r = 1 := by
  have hs : (σ a) ^ r = 1 := by rw [← map_pow, har, map_one]
  have hroots (i : Fin 4) : (weights σ a i) ^ r = 1 := by
    fin_cases i <;> simp [weights, mul_pow, inv_pow, har, hs]
  have hd : M.charpoly ∣ (X ^ r - 1 : F[X]) := by
    rw [hc]
    apply Finset.prod_dvd_of_coprime
    · intro i _ j _ hij
      exact pairwise_coprime_X_sub_C (weights_injective σ hσ a ha hne) hij
    · intro i _
      apply (dvd_iff_isRoot).mpr
      simp [Polynomial.IsRoot, hroots]
  have hz := aeval_eq_zero_of_dvd_aeval_eq_zero hd M.aeval_self_charpoly
  exact sub_eq_zero.mp (by simpa using hz)

end Kourovka2135.SuzukiBrandlMatrices
