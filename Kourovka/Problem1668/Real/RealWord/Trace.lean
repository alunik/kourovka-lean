import RealWord.Definitions
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Group
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace RealWord

open scoped MatrixGroups

variable {R : Type*} [CommRing R]

/-- The ordinary matrix trace of a determinant-one two-by-two matrix. -/
def tr (A : SL(2, R)) : R := Matrix.trace (A : Matrix (Fin 2) (Fin 2) R)

theorem tr_entries (A : SL(2, R)) : tr A = A 0 0 + A 1 1 := by
  exact Matrix.trace_fin_two _

@[simp] theorem tr_one : tr (1 : SL(2, R)) = 2 := by
  simp [tr]

theorem tr_mul_comm (A B : SL(2, R)) : tr (A * B) = tr (B * A) := by
  exact Matrix.trace_mul_comm (A : Matrix (Fin 2) (Fin 2) R) B

theorem tr_cycle (A B C : SL(2, R)) : tr (A * B * C) = tr (B * C * A) := by
  calc
    tr (A * B * C) = tr (A * (B * C)) := by rw [mul_assoc]
    _ = tr (B * C * A) := tr_mul_comm A (B * C)

@[simp] theorem tr_conj (A B : SL(2, R)) : tr (A * B * A⁻¹) = tr B := by
  rw [tr_cycle]
  simp

@[simp] theorem tr_inv (A : SL(2, R)) : tr A⁻¹ = tr A := by
  simp [tr, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
    Matrix.trace_fin_two, add_comm]

/-- The two-by-two trace skein identity. -/
theorem tr_skein (A B : SL(2, R)) :
    tr (A * B) + tr (A * B⁻¹) = tr A * tr B := by
  simp [tr, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
    Matrix.adjugate_fin_two, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  ring

theorem tr_skein_left (A B : SL(2, R)) :
    tr (A * B) + tr (A⁻¹ * B) = tr A * tr B := by
  rw [tr_mul_comm A B, tr_mul_comm A⁻¹ B, mul_comm (tr A)]
  exact tr_skein B A

theorem tr_square (A : SL(2, R)) : tr (A * A) = tr A ^ 2 - 2 := by
  have h := tr_skein A A
  simp only [mul_inv_cancel, tr_one] at h
  linear_combination h

/-- Fricke's commutator trace identity over a commutative ring. -/
theorem tr_fricke (A B : SL(2, R)) :
    tr (comm A B) = tr A ^ 2 + tr B ^ 2 + tr (A * B) ^ 2 -
      tr A * tr B * tr (A * B) - 2 := by
  have h1 := tr_skein (A * B) B
  have hc1 : A * B * B⁻¹ = A := by group
  rw [hc1] at h1
  have h2 := tr_skein_left A (A * B * B)
  have hc2 : A⁻¹ * (A * B * B) = B * B := by group
  have hc3 : A * (A * B * B) = A * A * B * B := by group
  rw [hc2, hc3, tr_square] at h2
  have h3 := tr_skein (A * B) (A⁻¹ * B⁻¹)
  have hc4 : A * B * (A⁻¹ * B⁻¹) = comm A B := by simp [comm, mul_assoc]
  have hc5 : A * B * (A⁻¹ * B⁻¹)⁻¹ = A * B * B * A := by group
  have hc6 : tr (A⁻¹ * B⁻¹) = tr (A * B) := by
    rw [← tr_inv (A⁻¹ * B⁻¹)]
    simp only [mul_inv_rev, inv_inv]
    exact tr_mul_comm B A
  rw [hc4, hc5, hc6] at h3
  have hc7 : tr (A * B * B * A) = tr (A * A * B * B) := by
    simpa only [mul_assoc] using tr_mul_comm (A * B * B) A
  rw [hc7] at h3
  linear_combination h3 - h2 - tr A * h1

/-- A six-letter trace used in the short derivation of the base word. -/
theorem tr_comm_mul_inv_mul (A C : SL(2, R)) (hC : tr C = tr A) :
    tr (comm A C * (A⁻¹ * C)) = tr A ^ 2 - tr (A * C) * (tr (comm A C) - 1) := by
  let c := comm A C
  let M := A * C * A⁻¹
  let N := C⁻¹ * A⁻¹ * C
  have h1 := tr_skein_left c (A * C)
  have hc1 : c⁻¹ * (A * C) = C * A := by
    dsimp [c, comm]
    group
  rw [hc1, tr_mul_comm C A] at h1
  have h2 := tr_skein M N
  have hM : tr M = tr A := by simpa [M] using hC
  have hN : tr N = tr A := by
    dsimp [N]
    have h := tr_conj C⁻¹ A⁻¹
    simpa using h
  have hc2 : M * N = c * (A⁻¹ * C) := by
    dsimp [M, N, c, comm]
    group
  have hc3 : M * N⁻¹ = c * (A * C) := by
    dsimp [M, N, c, comm]
    group
  rw [hM, hN, hc2, hc3] at h2
  change tr (c * (A⁻¹ * C)) = tr A ^ 2 - tr (A * C) * (tr c - 1)
  linear_combination h2 - h1

/-- Exact trace of the base word on any equal-trace input pair. -/
theorem tr_base (A C : SL(2, R)) (hC : tr C = tr A) :
    tr (base A C) = tracePoly (tr A ^ 2) (tr (A * C)) := by
  let c := comm A C
  let D := A⁻¹ * C
  let u := A * c * A⁻¹
  let v := C * c⁻¹ * C⁻¹
  have hc : tr c = tr (A * C) ^ 2 - tr (A * C) * tr A ^ 2 +
      2 * tr A ^ 2 - 2 := by
    have h := tr_fricke A C
    rw [hC] at h
    dsimp [c]
    linear_combination h
  have hd : tr D = tr A ^ 2 - tr (A * C) := by
    have h := tr_skein_left A C
    rw [hC] at h
    dsimp [D]
    linear_combination h
  have hj : tr (c * D) = tr A ^ 2 - tr (A * C) * (tr c - 1) :=
    tr_comm_mul_inv_mul A C hC
  have hprod : tr (u * v) = tr (comm c D) := by
    have hg : A⁻¹ * (u * v) * (A⁻¹)⁻¹ = comm c D := by
      dsimp [u, v, D, comm]
      group
    calc
      tr (u * v) = tr (A⁻¹ * (u * v) * (A⁻¹)⁻¹) := (tr_conj A⁻¹ (u * v)).symm
      _ = tr (comm c D) := congrArg tr hg
  have hu : tr u = tr c := by simp [u]
  have hv : tr v = tr c := by simp [v]
  have hr := tr_fricke c D
  have hb := tr_fricke u v
  rw [hu, hv, hprod] at hb
  simp only [hr, hj, hd, hc] at hb
  change tr (comm u v) = tracePoly (tr A ^ 2) (tr (A * C))
  unfold tracePoly hpoly
  linear_combination hb

/-- The literal conjugate-input substitution for the global word. -/
theorem tr_value (A B : SL(2, R)) :
    tr (value A B) = tracePoly (tr A ^ 2) (tr (A * (B * A * B⁻¹))) := by
  exact tr_base A (B * A * B⁻¹) (tr_conj B A)

end RealWord
