import Mathlib.GroupTheory.PGroup
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.End

/-! An actual invariant character is obtained by an orbit norm followed
by the inverse coprime power automorphism of an abelian p-group.
It agrees with the original character on every fixed element. No finite
group, character-extension, or first-cohomology theorem is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.CoprimeCharacterAveraging

open scoped BigOperators

variable {A B : Type*} [CommGroup A] [Monoid B]
variable (τ : MulAut A) (m : ℕ)

/-- The actual product of a finite orbit segment, as a group homomorphism. -/
def norm : A →* A where
  toFun a := ∏ i ∈ Finset.range m, (τ ^ i) a
  map_one' := by simp
  map_mul' a b := by simp only [map_mul, Finset.prod_mul_distrib]

@[simp] theorem norm_apply (a : A) : norm τ m a = ∏ i ∈ Finset.range m, (τ ^ i) a := rfl

/-- Closing the orbit makes its actual norm invariant. -/
theorem norm_invariant (hτ : τ ^ m = 1) (a : A) : norm τ m (τ a) = norm τ m a := by
  have hstep (i : ℕ) : (τ ^ i) (τ a) = (τ ^ (i + 1)) a := by
    rw [pow_succ]
    rfl
  have hprod : norm τ m (τ a) * a = norm τ m a * a := by
    calc
      norm τ m (τ a) * a = (∏ i ∈ Finset.range (m + 1), (τ ^ i) a) := by
        rw [Finset.prod_range_succ']
        simp only [norm_apply, hstep, pow_zero, MulAut.one_apply]
      _ = norm τ m a * a := by
        rw [Finset.prod_range_succ, hτ]
        rfl
  exact mul_right_cancel hprod

/-- On a fixed element the actual orbit norm is the corresponding power. -/
theorem norm_of_fixed (a : A) (ha : τ a = a) : norm τ m a = a ^ m := by
  have hpow (i : ℕ) : (τ ^ i) a = a := by
    induction i with
    | zero => rfl
    | succ i hi =>
      rw [pow_succ]
      change (τ ^ i) (τ a) = a
      rw [ha, hi]
  simp only [norm_apply, hpow, Finset.prod_const, Finset.card_range]

variable {p : ℕ} (hA : IsPGroup p A) (hm : Nat.Coprime p m)

/-- Coprime powering is an actual automorphism of the abelian p-group. -/
def powerAut : MulAut A :=
  MulEquiv.ofBijective (powMonoidHom m) (hA.powEquiv hm).bijective

@[simp] theorem powerAut_apply (a : A) : powerAut m hA hm a = a ^ m := rfl

/-- Average a character by correcting the orbit norm with inverse powering. -/
def average (χ : A →* B) : A →* B :=
  χ.comp ((powerAut m hA hm).symm.toMonoidHom.comp (norm τ m))

/-- The averaged character is actually invariant under the given automorphism. -/
theorem average_invariant (hτ : τ ^ m = 1) (χ : A →* B) (a : A) :
    average τ m hA hm χ (τ a) = average τ m hA hm χ a := by
  change χ ((powerAut m hA hm).symm (norm τ m (τ a))) =
    χ ((powerAut m hA hm).symm (norm τ m a))
  rw [norm_invariant τ m hτ]

/-- Averaging preserves every original value on the fixed subgroup. -/
theorem average_of_fixed (χ : A →* B) (a : A) (ha : τ a = a) :
    average τ m hA hm χ a = χ a := by
  change χ ((powerAut m hA hm).symm (norm τ m a)) = χ a
  rw [norm_of_fixed τ m a ha]
  exact congrArg χ ((powerAut m hA hm).symm_apply_apply a)

end Kourovka2135.CoprimeCharacterAveraging
