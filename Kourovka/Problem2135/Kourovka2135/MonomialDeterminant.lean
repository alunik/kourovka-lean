import Mathlib.LinearAlgebra.Determinant
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Int.Order.Units
import Mathlib.Data.Nat.Prime.Basic

/-! Determinants of actual weighted coordinate permutations.
If every coordinate weight is killed by n, the determinant is killed by 2*n.
A coprime power relation on the actual operator then forces determinant one.
The empty coordinate type is allowed; no monomial classification is assumed. -/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.MonomialDeterminant

open scoped BigOperators

variable {k ι : Type*} [Field k] [Fintype ι] [DecidableEq ι]
variable (L : Module.End k (ι → k)) (σ : Equiv.Perm ι) (a : ι → k)
variable (hL : ∀ (x : ι → k) (i : ι), L x i = a i * x (σ i))

include hL in
/-- The matrix of the actual operator is a diagonal matrix with permuted columns. -/
theorem toMatrix_eq :
    LinearMap.toMatrix' L = (Matrix.diagonal a).submatrix id σ.symm := by
  ext i j
  rw [LinearMap.toMatrix'_apply, hL]
  simp only [Matrix.submatrix_apply, id_eq, Matrix.diagonal_apply]
  by_cases h : σ i = j
  · subst j
    simp
  · have h' : i ≠ σ.symm j := by
      intro hi
      apply h
      simpa only [Equiv.apply_symm_apply] using congrArg σ hi
    simp [h, h']

include hL in
/-- The determinant is the sign of the coordinate permutation times the product of weights. -/
theorem det_eq_sign_mul_prod :
    LinearMap.det L = ((Equiv.Perm.sign σ : ℤ) : k) * ∏ i, a i := by
  classical
  rw [← LinearMap.det_toMatrix' L, toMatrix_eq L σ a hL,
    Matrix.det_permute', Matrix.det_diagonal, Equiv.Perm.sign_symm]

/-- The scalar image of any permutation sign has square one. -/
theorem sign_cast_sq : (((Equiv.Perm.sign σ : ℤ) : k)) ^ 2 = 1 := by
  have h := congrArg (Int.castRingHom k) (Int.isUnit_sq (Equiv.Perm.sign σ).isUnit)
  simpa only [map_pow, map_one, Int.coe_castRingHom] using h

include hL in
/-- A common exponent for the weights gives twice that exponent for the determinant. -/
theorem det_pow_twice_eq_one (n : ℕ) (ha : ∀ i, a i ^ n = 1) :
    LinearMap.det L ^ (2 * n) = 1 := by
  classical
  have hp : (∏ i, a i) ^ n = 1 := by
    rw [← Finset.prod_pow]
    simp only [ha, Finset.prod_const_one]
  have hp' : (∏ i, a i) ^ (2 * n) = 1 := by
    rw [Nat.mul_comm 2 n, pow_mul, hp, one_pow]
  have hs : (((Equiv.Perm.sign σ : ℤ) : k)) ^ (2 * n) = 1 := by
    rw [pow_mul, sign_cast_sq (k := k) σ, one_pow]
  rw [det_eq_sign_mul_prod L σ a hL, mul_pow, hs, hp', mul_one]

include hL in
/-- Coprime annihilating powers of the determinant force it to be one. -/
theorem det_eq_one_of_coprime_pow (n m : ℕ)
    (ha : ∀ i, a i ^ n = 1) (hpow : L ^ m = 1) (hcop : (2 * n).Coprime m) :
    LinearMap.det L = 1 := by
  have hn : LinearMap.det L ^ (2 * n) = 1 := det_pow_twice_eq_one L σ a hL n ha
  have hm : LinearMap.det L ^ m = 1 := by
    simpa only [map_pow, map_one] using congrArg LinearMap.det hpow
  apply orderOf_eq_one_iff.mp
  exact Nat.eq_one_of_dvd_coprimes hcop
    (orderOf_dvd_of_pow_eq_one hn) (orderOf_dvd_of_pow_eq_one hm)

include hL in
/-- Weights of two-power exponent give a two-power exponent for the determinant. -/
theorem det_pow_twoPower_eq_one (r : ℕ) (ha : ∀ i, a i ^ (2 ^ r) = 1) :
    LinearMap.det L ^ (2 ^ (r + 1)) = 1 := by
  simpa only [pow_succ, Nat.mul_comm] using det_pow_twice_eq_one L σ a hL (2 ^ r) ha

include hL in
/-- An actual odd-order operator with two-power coordinate weights has determinant one. -/
theorem det_eq_one_of_odd_pow (r m : ℕ)
    (ha : ∀ i, a i ^ (2 ^ r) = 1) (hm : Odd m) (hpow : L ^ m = 1) :
    LinearMap.det L = 1 := by
  apply det_eq_one_of_coprime_pow L σ a hL (2 ^ r) m ha hpow
  exact Nat.coprime_mul_iff_left.mpr
    ⟨hm.coprime_two_left, hm.coprime_two_left.pow_left r⟩

end Kourovka2135.MonomialDeterminant
