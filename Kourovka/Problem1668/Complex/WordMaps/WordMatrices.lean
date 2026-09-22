import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.Algebra.Group.Conj
import Mathlib.Tactic.FinCases

/-!
# Elementary polynomial matrix specialization

The two generators are sent to the upper shear with parameter one and the lower
shear with parameter X. Each alternating block has degree at most one. The top
coefficient of a product is the product of its top coefficient matrices; the
trace of this product is the product of all integer exponents.
-/

noncomputable section

namespace WordMaps

open Matrix Polynomial
open scoped MatrixGroups

section Elementary

variable {R : Type*} [CommRing R]

def wordUpper (t : R) : SL(2, R) :=
  ⟨!![1, t; 0, 1], by simp [Matrix.det_fin_two]⟩

def wordLower (t : R) : SL(2, R) :=
  ⟨!![1, 0; t, 1], by simp [Matrix.det_fin_two]⟩

@[simp] theorem wordUpper_val (t : R) : (wordUpper t).val = !![1, t; 0, 1] := rfl
@[simp] theorem wordLower_val (t : R) : (wordLower t).val = !![1, 0; t, 1] := rfl

@[simp] theorem wordUpper_zero : wordUpper (0 : R) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [wordUpper]

@[simp] theorem wordLower_zero : wordLower (0 : R) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [wordLower]

theorem wordUpper_add (s t : R) : wordUpper (s + t) = wordUpper s * wordUpper t := by
  apply Subtype.ext
  change !![1, s + t; 0, 1] = (!![1, s; 0, 1] : Matrix (Fin 2) (Fin 2) R) *
    !![1, t; 0, 1]
  simp [add_comm]

theorem wordLower_add (s t : R) : wordLower (s + t) = wordLower s * wordLower t := by
  apply Subtype.ext
  change !![1, 0; s + t, 1] = (!![1, 0; s, 1] : Matrix (Fin 2) (Fin 2) R) *
    !![1, 0; t, 1]
  simp

@[simp] theorem wordUpper_neg (t : R) : wordUpper (-t) = (wordUpper t)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← wordUpper_add, neg_add_cancel, wordUpper_zero]

@[simp] theorem wordLower_neg (t : R) : wordLower (-t) = (wordLower t)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← wordLower_add, neg_add_cancel, wordLower_zero]

theorem wordUpper_zpow (t : R) (n : ℤ) : wordUpper t ^ n = wordUpper ((n : R) * t) := by
  induction n with
  | zero => simp
  | succ n ih => simp [zpow_add, ih, add_mul, wordUpper_add]
  | pred n ih => simp [sub_eq_add_neg, zpow_add, ih, add_mul, wordUpper_add]

theorem wordLower_zpow (t : R) (n : ℤ) : wordLower t ^ n = wordLower ((n : R) * t) := by
  induction n with
  | zero => simp
  | succ n ih => simp [zpow_add, ih, add_mul, wordLower_add]
  | pred n ih => simp [sub_eq_add_neg, zpow_add, ih, add_mul, wordLower_add]

end Elementary

variable (K : Type*) [Field K]

def wordPolynomialGenerators (i : Fin 2) : SL(2, Polynomial K) :=
  if i = 0 then wordUpper 1 else wordLower X

@[simp] theorem wordPolynomialGenerators_zero :
    wordPolynomialGenerators K 0 = wordUpper 1 := by simp [wordPolynomialGenerators]

@[simp] theorem wordPolynomialGenerators_one :
    wordPolynomialGenerators K 1 = wordLower X := by simp [wordPolynomialGenerators]

def wordTrace (w : FreeGroup (Fin 2)) : Polynomial K :=
  Matrix.trace (FreeGroup.lift (wordPolynomialGenerators K) w).val

theorem wordTrace_eq_of_isConj {w v : FreeGroup (Fin 2)} (h : IsConj w v) :
    wordTrace K w = wordTrace K v := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp h
  simp only [wordTrace, map_mul, map_inv, SpecialLinearGroup.coe_mul]
  rw [Matrix.trace_mul_cycle]
  rw [← SpecialLinearGroup.coe_mul, inv_mul_cancel, SpecialLinearGroup.coe_one, Matrix.one_mul]

def wordBlockMatrix (p : ℤ × ℤ) : Matrix (Fin 2) (Fin 2) (Polynomial K) :=
  !![1 + (p.1 : Polynomial K) * (p.2 : Polynomial K) * X, (p.1 : Polynomial K);
    (p.2 : Polynomial K) * X, 1]

theorem wordBlockMatrix_eq (p : ℤ × ℤ) :
    wordBlockMatrix K p = ((wordPolynomialGenerators K 0 ^ p.1) *
      (wordPolynomialGenerators K 1 ^ p.2)).val := by
  simp [wordBlockMatrix, wordUpper_zpow, wordLower_zpow,
    SpecialLinearGroup.coe_mul, mul_assoc]

def wordLeadingMatrix (p : ℤ × ℤ) : Matrix (Fin 2) (Fin 2) K :=
  !![(p.1 : K) * (p.2 : K), 0; (p.2 : K), 0]

variable {K}

def matrixCoeff (M : Matrix (Fin 2) (Fin 2) (Polynomial K)) (n : ℕ) :
    Matrix (Fin 2) (Fin 2) K := fun i j => (M i j).coeff n

def MatrixDegreeLE (M : Matrix (Fin 2) (Fin 2) (Polynomial K)) (n : ℕ) : Prop :=
  ∀ i j, (M i j).natDegree ≤ n

theorem matrixDegreeLE_mul {A B : Matrix (Fin 2) (Fin 2) (Polynomial K)} {m n : ℕ}
    (hA : MatrixDegreeLE A m) (hB : MatrixDegreeLE B n) :
    MatrixDegreeLE (A * B) (m + n) := by
  intro i j
  simp only [Matrix.mul_apply]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k _
  exact (Polynomial.natDegree_mul_le).trans (Nat.add_le_add (hA i k) (hB k j))

theorem matrixCoeff_mul {A B : Matrix (Fin 2) (Fin 2) (Polynomial K)} {m n : ℕ}
    (hA : MatrixDegreeLE A m) (hB : MatrixDegreeLE B n) :
    matrixCoeff (A * B) (m + n) = matrixCoeff A m * matrixCoeff B n := by
  ext i j
  simp only [matrixCoeff, Matrix.mul_apply, finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro k _
  exact Polynomial.coeff_mul_add_eq_of_natDegree_le (hA i k) (hB k j)

theorem wordBlockMatrix_degree (p : ℤ × ℤ) : MatrixDegreeLE (wordBlockMatrix K p) 1 := by
  intro i j
  fin_cases i <;> fin_cases j
  · apply Polynomial.natDegree_add_le_of_degree_le
    · simp
    · apply (Polynomial.natDegree_mul_le).trans
      have hab : ((p.1 : Polynomial K) * (p.2 : Polynomial K)).natDegree ≤ 0 :=
        Polynomial.natDegree_mul_le.trans (by simp)
      exact Nat.add_le_add hab Polynomial.natDegree_X_le
  · simp [wordBlockMatrix]
  · simp only [wordBlockMatrix, Matrix.of_apply]
    apply (Polynomial.natDegree_mul_le).trans
    simp
  · simp [wordBlockMatrix]

theorem wordBlockMatrix_coeff (p : ℤ × ℤ) :
    matrixCoeff (wordBlockMatrix K p) 1 = wordLeadingMatrix K p := by
  have hc (z : ℤ) : (z : Polynomial K).coeff 1 = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (by simp)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixCoeff, wordBlockMatrix, wordLeadingMatrix, Polynomial.coeff_mul_X,
      Polynomial.coeff_one, hc]

theorem wordBlockProduct_degree (bs : List (ℤ × ℤ)) :
    MatrixDegreeLE (bs.map (wordBlockMatrix K)).prod bs.length := by
  induction bs with
  | nil =>
    intro i j
    simp only [List.map_nil, List.prod_nil, List.length_nil, Matrix.one_apply]
    split <;> simp
  | cons p bs ih =>
    simpa [Nat.add_comm] using matrixDegreeLE_mul (wordBlockMatrix_degree p) ih

theorem wordBlockProduct_coeff (bs : List (ℤ × ℤ)) :
    matrixCoeff (bs.map (wordBlockMatrix K)).prod bs.length =
      (bs.map (wordLeadingMatrix K)).prod := by
  induction bs with
  | nil =>
    ext i j
    simp only [List.map_nil, List.prod_nil, List.length_nil, matrixCoeff, Matrix.one_apply]
    split <;> simp
  | cons p bs ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons]
    rw [Nat.add_comm, matrixCoeff_mul (wordBlockMatrix_degree p) (wordBlockProduct_degree bs),
      wordBlockMatrix_coeff, ih]

theorem wordLeadingProduct_zero_zero (bs : List (ℤ × ℤ)) :
    ((bs.map (wordLeadingMatrix K)).prod) 0 0 =
      (bs.map fun p => (p.1 : K) * (p.2 : K)).prod := by
  induction bs with
  | nil => simp
  | cons p bs ih =>
    simp [wordLeadingMatrix, Matrix.mul_apply, Fin.sum_univ_two, ih]

theorem wordLeadingProduct_zero_one (bs : List (ℤ × ℤ)) :
    ((bs.map (wordLeadingMatrix K)).prod) 0 1 = 0 := by
  induction bs with
  | nil => simp
  | cons p bs ih =>
    simp [wordLeadingMatrix, Matrix.mul_apply, Fin.sum_univ_two, ih]

theorem wordLeadingProduct_one_one {bs : List (ℤ × ℤ)} (hbs : bs ≠ []) :
    ((bs.map (wordLeadingMatrix K)).prod) 1 1 = 0 := by
  cases bs with
  | nil => contradiction
  | cons p bs =>
    simp [wordLeadingMatrix, Matrix.mul_apply, Fin.sum_univ_two, wordLeadingProduct_zero_one]

theorem wordBlockProduct_trace_coeff {bs : List (ℤ × ℤ)} (hbs : bs ≠ []) :
    (Matrix.trace (bs.map (wordBlockMatrix K)).prod).coeff bs.length =
      (bs.map fun p => (p.1 : K) * (p.2 : K)).prod := by
  have hc := wordBlockProduct_coeff (K := K) bs
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 0 0) hc
  have h11 := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 1 1) hc
  simpa [Matrix.trace_fin_two, matrixCoeff, wordLeadingProduct_zero_zero,
    wordLeadingProduct_one_one hbs] using congrArg₂ (· + ·) h00 h11

variable [CharZero K]

theorem wordBlockProduct_trace_natDegree {bs : List (ℤ × ℤ)} (hbs : bs ≠ [])
    (hnz : ∀ p ∈ bs, p.1 ≠ 0 ∧ p.2 ≠ 0) :
    (Matrix.trace (bs.map (wordBlockMatrix K)).prod).natDegree = bs.length := by
  have hp : (bs.map fun p => (p.1 : K) * (p.2 : K)).prod ≠ 0 := by
    apply List.prod_ne_zero
    intro hz
    obtain ⟨p, hp, hpzero⟩ := List.mem_map.mp hz
    exact (mul_ne_zero (by exact_mod_cast (hnz p hp).1)
      (by exact_mod_cast (hnz p hp).2)) hpzero
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · rw [Matrix.trace_fin_two]
    exact Polynomial.natDegree_add_le_of_degree_le
      (wordBlockProduct_degree bs 0 0) (wordBlockProduct_degree bs 1 1)
  · rwa [wordBlockProduct_trace_coeff hbs]

theorem wordBlockProduct_trace_nonconstant {bs : List (ℤ × ℤ)} (hbs : bs ≠ [])
    (hnz : ∀ p ∈ bs, p.1 ≠ 0 ∧ p.2 ≠ 0) :
    (Matrix.trace (bs.map (wordBlockMatrix K)).prod).natDegree ≠ 0 := by
  rw [wordBlockProduct_trace_natDegree hbs hnz]
  simpa using hbs

end WordMaps
