import Kourovka2135.SuzukiBrandlCommutator

/-! Actual orders of Brandl's two Suzuki elements and their commutator,
proved from the explicit split quartic and Cayley-Hamilton. -/

set_option autoImplicit false
noncomputable section
namespace Kourovka2135.SuzukiBrandlOrders

open Matrix Polynomial SuzukiBrandlMatrices SuzukiBrandlCommutator SuzukiTorusMovingRank
open scoped Matrix MatrixGroups Polynomial

abbrev lambda (m : ℕ) (x : (K m)ˣ) : K m := (x : K m) ^ (2 ^ m)

def parameter (m : ℕ) (x : (K m)ˣ) : K m :=
  (tits m).symm (traceParameter (tits m) (lambda m x))

def partner (m : ℕ) (x : (K m)ˣ) : G m := y m (parameter m x)

theorem charpoly_torus (m : ℕ) (x : (K m)ˣ) :
    (matrixHom m (torusHom m x)).charpoly =
      ∏ i : Fin 4, (X - C (weights (tits m) (lambda m x) i)) := by
  rw [matrixHom_torus, diagonalPair, Matrix.charpoly_diagonal]
  rfl

theorem charpoly_partner (m : ℕ) (x : (K m)ˣ) :
    (matrixHom m (partner m x)).charpoly =
      ∏ i : Fin 4, (X - C (weights (tits m) (lambda m x) i)) := by
  rw [partner, matrixHom_y]
  simp only [parameter, RingEquiv.apply_symm_apply]
  exact charpoly_yMatrix_parameter (tits m) (tits_sq m) _ (pow_ne_zero _ x.ne_zero)

theorem charpoly_commutator (m : ℕ) (x : (K m)ˣ) :
    (matrixHom m (paperCommutator (torusHom m x) (partner m x))).charpoly =
      ∏ i : Fin 4, (X - C (weights (tits m) ((lambda m x) ^ 2) i)) := by
  rw [partner, matrixHom_commutator, charpoly_upperCommutator,
    diagonalPair, Matrix.charpoly_diagonal]
  simp only [weights, lambda, map_pow, mul_pow]

theorem lambda_pow_eq_one (m : ℕ) (x : (K m)ˣ) (r : ℕ) (hx : x ^ r = 1) :
    (lambda m x) ^ r = 1 := by
  have hh : (x : K m) ^ r = 1 := by simpa using congrArg Units.val hx
  calc
    _ = ((x : K m) ^ r) ^ (2 ^ m) := by simp only [← pow_mul, mul_comm]
    _ = 1 := by rw [hh, one_pow]

theorem partner_ne_one (m : ℕ) (x : (K m)ˣ) : partner m x ≠ 1 :=
  y_ne_one m (parameter m x)

theorem commutator_ne_one (m : ℕ) (x : (K m)ˣ) (hx : x ≠ 1) :
    paperCommutator (torusHom m x) (partner m x) ≠ 1 := by
  intro he
  have hh := congrArg (fun g : G m => matrixHom m g 2 2) he
  rw [partner, matrixHom_commutator] at hh
  have hs : (lambda m x) ^ 2 = 1 := by simpa [upperCommutator, lambda] using hh
  exact middle_ne_one m x hx ((sq_eq_one_iff _).mp hs)

theorem partner_pow_eq_one (m : ℕ) (x : (K m)ˣ) (hx : x ≠ 1)
    (r : ℕ) (hr : x ^ r = 1) : (partner m x) ^ r = 1 := by
  apply matrixHom_injective m
  rw [map_pow, map_one]
  exact pow_eq_one_of_charpoly_weights (tits m) (tits_sq m) (lambda m x)
    (pow_ne_zero _ x.ne_zero) (middle_ne_one m x hx) r
    (lambda_pow_eq_one m x r hr) _ (charpoly_partner m x)

theorem commutator_pow_eq_one (m : ℕ) (x : (K m)ˣ) (hx : x ≠ 1)
    (r : ℕ) (hr : x ^ r = 1) :
    (paperCommutator (torusHom m x) (partner m x)) ^ r = 1 := by
  have ha : (lambda m x) ^ 2 ≠ 1 := fun h =>
    middle_ne_one m x hx ((sq_eq_one_iff _).mp h)
  have har : ((lambda m x) ^ 2) ^ r = 1 := by
    rw [← pow_mul, Nat.mul_comm 2 r, pow_mul, lambda_pow_eq_one m x r hr, one_pow]
  apply matrixHom_injective m
  rw [map_pow, map_one]
  exact pow_eq_one_of_charpoly_weights (tits m) (tits_sq m) ((lambda m x) ^ 2)
    (pow_ne_zero _ (pow_ne_zero _ x.ne_zero)) ha r har _ (charpoly_commutator m x)

theorem partner_order (m : ℕ) (r : ℕ) (hr : r.Prime)
    (x : (K m)ˣ) (hx : orderOf x = r) : orderOf (partner m x) = r := by
  have hne : x ≠ 1 := by rintro rfl; simp only [orderOf_one] at hx; exact hr.ne_one hx.symm
  have hp := partner_pow_eq_one m x hne r (by rw [← hx]; exact pow_orderOf_eq_one x)
  rcases (Nat.dvd_prime hr).mp (orderOf_dvd_iff_pow_eq_one.mpr hp) with h | h
  · exact False.elim (partner_ne_one m x (orderOf_eq_one_iff.mp h))
  · exact h

theorem commutator_order (m : ℕ) (r : ℕ) (hr : r.Prime)
    (x : (K m)ˣ) (hx : orderOf x = r) :
    orderOf (paperCommutator (torusHom m x) (partner m x)) = r := by
  have hne : x ≠ 1 := by rintro rfl; simp only [orderOf_one] at hx; exact hr.ne_one hx.symm
  have hp := commutator_pow_eq_one m x hne r (by rw [← hx]; exact pow_orderOf_eq_one x)
  rcases (Nat.dvd_prime hr).mp (orderOf_dvd_iff_pow_eq_one.mpr hp) with h | h
  · exact False.elim (commutator_ne_one m x hne (orderOf_eq_one_iff.mp h))
  · exact h

end Kourovka2135.SuzukiBrandlOrders
