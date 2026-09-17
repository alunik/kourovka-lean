import Mathlib.GroupTheory.OrderOfElement
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.NormNum

set_option autoImplicit false

namespace Kourovka.Problem2153

universe u

/-- The two scalar exponent certificates force the identity, with no field-specific axiom. -/
theorem eq_one_of_pow_26_eq_one_of_pow_7_eq_one {M : Type u} [Monoid M] (a : M)
    (h26 : a ^ 26 = 1) (h7 : a ^ 7 = 1) : a = 1 := by
  have hd26 : orderOf a ∣ 26 := orderOf_dvd_iff_pow_eq_one.mpr h26
  have hd7 : orderOf a ∣ 7 := orderOf_dvd_iff_pow_eq_one.mpr h7
  have hd1 : orderOf a ∣ 1 := by simpa using Nat.dvd_gcd hd26 hd7
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_one hd1)

/-- After a projective-frame argument makes a matrix scalar, determinant one and the
multiplicative exponent of GF(8) eliminate that scalar. -/
theorem scalar_matrix_eq_one {K : Type u} [CommRing K]
    (A : Matrix (Fin 26) (Fin 26) K) (a : K)
    (hScalar : A = a • (1 : Matrix (Fin 26) (Fin 26) K))
    (hDet : Matrix.det A = 1) (h7 : a ^ 7 = 1) : A = 1 := by
  have h26 : a ^ 26 = 1 := by
    simpa only [hScalar, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] using hDet
  rw [hScalar, eq_one_of_pow_26_eq_one_of_pow_7_eq_one a h26 h7, one_smul]

/-- In a field with eight elements, determinant one alone eliminates a scalar 26 by 26
matrix. The scalar's nonvanishing and seventh-power identity are derived. -/
theorem scalar_matrix_eq_one_of_card_eight {K : Type u} [Field K] [Fintype K]
    (hCard : Fintype.card K = 8) (A : Matrix (Fin 26) (Fin 26) K) (a : K)
    (hScalar : A = a • (1 : Matrix (Fin 26) (Fin 26) K))
    (hDet : Matrix.det A = 1) : A = 1 := by
  have h26 : a ^ 26 = 1 := by
    simpa only [hScalar, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] using hDet
  have ha : a ≠ 0 := by
    intro hz
    simp [hz] at h26
  apply scalar_matrix_eq_one A a hScalar hDet
  simpa only [hCard, show (8 : ℕ) - 1 = 7 from rfl] using
    FiniteField.pow_card_sub_one_eq_one a ha

#print axioms eq_one_of_pow_26_eq_one_of_pow_7_eq_one
#print axioms scalar_matrix_eq_one
#print axioms scalar_matrix_eq_one_of_card_eight

end Kourovka.Problem2153
