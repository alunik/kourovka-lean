import Kourovka2135.ScalarWeightAdditiveMaps
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic.LinearCombination

/-! Elementary root-count obstructions to additive power weights.
These lemmas rule out the three unwanted natural Suzuki Borel weights for
q > 8. They do not assert a bound for q = 8: the inverse-cubic weight is
indeed Frobenius on F8. No field-embedding classification is used.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.ScalarPowerAdditivity

open Polynomial
variable {F k : Type*} [Field F] [Finite F] [Field k]

/-- Inverse n-th power cannot be additive when the field has more than
2n+2 elements. The obstruction is a polynomial of degree exactly 2n. -/
theorem inverse_power_not_additive [CharP F 2] (n : ℕ) (hn : 0 < n)
    (hcard : 2 * n + 2 < Nat.card F) :
    ¬ ∀ x y : F, ((x + y) ^ n)⁻¹ = (x ^ n)⁻¹ + (y ^ n)⁻¹ := by
  classical
  let := Fintype.ofFinite F
  intro hadd
  let A : F[X] := X ^ n
  let B : F[X] := (X + C 1) ^ n
  let R : F[X] := A * B + B
  let P : F[X] := R - A
  have hA : A.natDegree = n := natDegree_X_pow n
  have hB : B.natDegree = n := by
    simp only [B, (monic_X_add_C (1 : F)).natDegree_pow, natDegree_X_add_C, mul_one]
  have hAB : (A * B).natDegree = 2 * n := by
    rw [(monic_X.pow n).natDegree_mul ((monic_X_add_C (1 : F)).pow n), hA, hB]
    omega
  have hR : R.natDegree = 2 * n := by
    change (A * B + B).natDegree = _
    rw [natDegree_add_eq_left_of_natDegree_lt (by rw [hB, hAB]; omega), hAB]
  have hP : P.natDegree = 2 * n := by
    change (R - A).natDegree = _
    rw [natDegree_sub_eq_left_of_natDegree_lt (by rw [hA, hR]; omega), hR]
  have hP0 : P ≠ 0 := by
    intro he
    rw [he, natDegree_zero] at hP
    omega
  let S : Finset F := (Finset.univ.erase 0).erase 1
  have hScard : S.card = Fintype.card F - 2 := by
    simp [S, Finset.card_erase_of_mem, one_ne_zero, Nat.sub_sub]
  have hroot : S.val ⊆ P.roots := by
    intro x hx
    have hxS : x ∈ S := hx
    have hx0 : x ≠ 0 := (Finset.mem_erase.mp (Finset.mem_erase.mp hxS).2).1
    have hx1 : x ≠ 1 := (Finset.mem_erase.mp hxS).1
    have hxp : x + 1 ≠ 0 := by
      intro he
      exact hx1 (by simpa only [CharTwo.neg_eq] using eq_neg_of_add_eq_zero_left he)
    apply (mem_roots hP0).mpr
    change P.eval x = 0
    have hb := hadd x 1
    simp only [one_pow, inv_one] at hb
    have hxnp : x ^ n ≠ 0 := pow_ne_zero _ hx0
    have hxpp : (x + 1) ^ n ≠ 0 := pow_ne_zero _ hxp
    field_simp [hxnp, hxpp] at hb
    simp only [P, R, A, B, eval_sub, eval_add, eval_mul, eval_pow, eval_X, eval_C]
    linear_combination -hb
  have hc := card_le_degree_of_subset_roots hroot
  rw [hScard, hP] at hc
  rw [Nat.card_eq_fintype_card] at hcard
  omega

/-- The positive binary-plus-one power fails additivity in a larger binary field. -/
theorem frobenius_plus_one_not_additive [CharP F 2]
    (m : ℕ) (hm : 0 < m) (hcard : 2 ^ m < Nat.card F) :
    ¬ ∀ x y : F, (x + y) ^ (2 ^ m + 1) = x ^ (2 ^ m + 1) + y ^ (2 ^ m + 1) := by
  classical
  let := Fintype.ofFinite F
  intro hadd
  let P : F[X] := X ^ (2 ^ m) + X
  have hr : 1 < 2 ^ m := Nat.one_lt_pow hm.ne' (by decide)
  have hdeg : P.natDegree = 2 ^ m := by
    change (X ^ (2 ^ m) + (X : F[X])).natDegree = _
    rw [natDegree_add_eq_left_of_natDegree_lt (by simpa using hr), natDegree_X_pow]
  have heval (x : F) : P.eval x = 0 := by
    have h := hadd x 1
    rw [pow_succ, add_pow_char_pow x 1 2 m] at h
    simp only [one_pow, pow_succ] at h
    simp only [P, eval_add, eval_pow, eval_X]
    linear_combination h
  have hzero : P = 0 := eq_zero_of_natDegree_lt_card_of_eval_eq_zero P
    Function.injective_id heval (by simpa only [hdeg, Nat.card_eq_fintype_card] using hcard)
  rw [hzero, natDegree_zero] at hdeg
  exact (Nat.pow_pos (by decide : 0 < 2)).ne' hdeg.symm

omit [Finite F] in
/-- Embeddings preserve and reflect the concrete nonadditivity obstruction. -/
theorem embedding_not_additive (σ : F →+* k) (w : F → F)
    (h : ¬ ∀ x y, w (x + y) = w x + w y) :
    ¬ ∀ x y, σ (w (x + y)) = σ (w x) + σ (w y) := by
  intro he
  apply h
  intro x y
  apply σ.injective
  rw [map_add]
  exact he x y

end Kourovka2135.ScalarPowerAdditivity
