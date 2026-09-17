import Kourovka.Problem2153.WilsonModel
import Kourovka.Problem2153.Core
import Mathlib.FieldTheory.Finite.Basic

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace Kourovka.Problem2153.WilsonModel

open Field8

/-- The actual distinct matrix witnesses make the generated group nontrivial. -/
instance ambient_nontrivial : Nontrivial ambient := nontrivial_of_ne X Y X_ne_Y

/-- This uses the actual Wilson involutions and their certified order-five product. -/
theorem ambient_nonabelian : Nonabelian ambient :=
  nonabelian_of_order_five witness_orders.1 witness_orders.2.1 witness_orders.2.2.2.1

/-- The explicit involution forces two to divide the ambient order. -/
theorem ambient_two_dvd_card : 2 ∣ Nat.card ambient := by
  rw [← witness_orders.2.1]
  exact orderOf_dvd_natCard X

/-- The explicit order-three element forces three to divide the ambient order. -/
theorem ambient_three_dvd_card : 3 ∣ Nat.card ambient := by
  rw [← order_C]
  exact orderOf_dvd_natCard C

/-- No group-order formula or identification with an abstract Ree group is needed here. -/
theorem ambient_two_smallest_primes : TwoSmallestPrimeDivisors (Nat.card ambient) 3 :=
  twoSmallestPrimeDivisors_three ambient_two_dvd_card ambient_three_dvd_card

private theorem fieldUnit_seventh (a : F8ˣ) : a ^ 7 = 1 := by
  apply Units.ext
  change (a : F8) ^ 7 = 1
  simpa only [Field8.card, show (8 : ℕ) - 1 = 7 from rfl] using
    FiniteField.pow_card_sub_one_eq_one (a : F8) a.ne_zero

/-- Determinants of elements of order coprime to seven are one in GL(26,8). -/
theorem det_eq_one_of_order_coprime_seven (g : GL26)
    (hCoprime : Nat.Coprime (orderOf g) 7) : Matrix.GeneralLinearGroup.det g = 1 := by
  let d : F8ˣ := Matrix.GeneralLinearGroup.det g
  have hp : d ^ orderOf g = 1 := by
    change (Matrix.GeneralLinearGroup.det g) ^ orderOf g = 1
    rw [← map_pow, pow_orderOf_eq_one, map_one]
  have hd : orderOf d ∣ 1 := by
    have h := Nat.dvd_gcd (orderOf_dvd_iff_pow_eq_one.mpr hp)
      (orderOf_dvd_iff_pow_eq_one.mpr (fieldUnit_seventh d))
    simpa only [hCoprime.gcd_eq_one] using h
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_one hd)

theorem det_tUnit : Matrix.GeneralLinearGroup.det tUnit = 1 :=
  det_eq_one_of_order_coprime_seven tUnit (by rw [order_tUnit]; decide)

theorem det_xUnit : Matrix.GeneralLinearGroup.det xUnit = 1 :=
  det_eq_one_of_order_coprime_seven xUnit (by rw [order_xUnit]; decide)

theorem det_rhoUnit : Matrix.GeneralLinearGroup.det rhoUnit = 1 :=
  det_eq_one_of_order_coprime_seven rhoUnit (by rw [order_rhoUnit]; decide)

theorem det_sigmaUnit : Matrix.GeneralLinearGroup.det sigmaUnit = 1 :=
  det_eq_one_of_order_coprime_seven sigmaUnit (by rw [order_sigmaUnit]; decide)

/-- Only 49 products of 26 field elements are checked, not permutation expansions of determinants. -/
theorem torusDiag_prod : ∀ a b : Fin 7, (∏ i : Fin 26, torusDiag a b i) = 1 := by
  decide +kernel

theorem det_torusUnit (a b : Fin 7) : Matrix.GeneralLinearGroup.det (torusUnit a b) = 1 := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
  rw [show ((torusUnit a b : GL26) : Mat) = Matrix.diagonal (torusDiag a b) from rfl,
    Matrix.det_diagonal, torusDiag_prod]

/-- Every actual generator belongs to the determinant kernel, hence so does its subgroup closure. -/
theorem ambient_le_det_ker : ambient ≤ (Matrix.GeneralLinearGroup.det (n := Fin 26) (R := F8)).ker := by
  apply (Subgroup.closure_le _).mpr
  intro g hg
  change Matrix.GeneralLinearGroup.det g = 1
  rcases hg with hg | ⟨⟨a, b⟩, rfl⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · exact det_tUnit
    · exact det_xUnit
    · exact det_rhoUnit
    · exact det_sigmaUnit
  · exact det_torusUnit a b

theorem ambient_det_unit (g : ambient) : Matrix.GeneralLinearGroup.det g.val = 1 :=
  ambient_le_det_ker g.property

/-- Determinant one for every matrix in the concrete ambient group. -/
theorem ambient_det (g : ambient) : Matrix.det (g.val : Mat) = 1 := by
  simpa only [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one] using
    congrArg (fun a : F8ˣ => (a : F8)) (ambient_det_unit g)

#print axioms ambient_nontrivial
#print axioms ambient_nonabelian
#print axioms ambient_two_smallest_primes
#print axioms torusDiag_prod
#print axioms ambient_le_det_ker
#print axioms ambient_det

end Kourovka.Problem2153.WilsonModel
