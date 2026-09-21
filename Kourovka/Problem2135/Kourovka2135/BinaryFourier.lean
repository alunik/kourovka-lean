import Mathlib.Algebra.Group.AddChar
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Tactic

/-! Integer-valued Fourier identities on finite binary vector spaces. -/
set_option autoImplicit false
namespace Kourovka2135.BinaryFourier
open scoped BigOperators
open Classical

def sign (a : ZMod 2) : ℤ := if a = 0 then 1 else -1

@[simp] theorem sign_zero : sign 0 = 1 := by decide
@[simp] theorem sign_one : sign 1 = -1 := by decide
@[simp] theorem sign_add (a b : ZMod 2) : sign (a + b) = sign a * sign b := by
  fin_cases a <;> fin_cases b <;> decide
@[simp] theorem sign_sub (a b : ZMod 2) : sign (a - b) = sign a * sign b := by
  fin_cases a <;> fin_cases b <;> decide
@[simp] theorem sign_sq (a : ZMod 2) : sign a ^ 2 = 1 := by
  fin_cases a <;> decide
@[simp] theorem sign_eq_one_iff (a : ZMod 2) : sign a = 1 ↔ a = 0 := by
  simp [sign]
@[simp] theorem sign_cast_two (a : ZMod 2) : (sign a : ZMod 2) = 1 := by
  fin_cases a <;> decide

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

def linearChar (ell : Module.Dual (ZMod 2) V) : AddChar V ℤ where
  toFun x := sign (ell x)
  map_zero_eq_one' := by simp
  map_add_eq_mul' x y := by simp

@[simp] theorem linearChar_eq_zero_iff (ell : Module.Dual (ZMod 2) V) :
    linearChar ell = 0 ↔ ell = 0 := by
  constructor
  · intro h
    ext x
    have hh := congrArg (fun f : AddChar V ℤ => f x) h
    change sign (ell x) = 1 at hh
    exact (sign_eq_one_iff _).mp hh
  · rintro rfl
    ext x
    simp [linearChar]

theorem sum_sign_linear [Fintype V] (ell : Module.Dual (ZMod 2) V) :
    ∑ x, sign (ell x) = if ell = 0 then (Fintype.card V : ℤ) else 0 := by
  classical
  have hs := AddChar.sum_eq_ite (linearChar ell)
  change (∑ x, sign (ell x)) = if linearChar ell = 0 then (Fintype.card V : ℤ) else 0 at hs
  simpa only [linearChar_eq_zero_iff] using hs

theorem sum_sign_dual [Fintype (Module.Dual (ZMod 2) V)] (x : V) :
    ∑ ell : Module.Dual (ZMod 2) V, sign (ell x) =
      if x = 0 then (Fintype.card (Module.Dual (ZMod 2) V) : ℤ) else 0 := by
  classical
  let ev : Module.Dual (ZMod 2) (Module.Dual (ZMod 2) V) :=
    { toFun := fun ell => ell x
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have he : ev = 0 ↔ x = 0 := by
    rw [LinearMap.ext_iff]
    exact Module.forall_dual_apply_eq_zero_iff (ZMod 2) x
  have hs := sum_sign_linear ev
  change (∑ ell : Module.Dual (ZMod 2) V, sign (ell x)) =
    if ev = 0 then (Fintype.card (Module.Dual (ZMod 2) V) : ℤ) else 0 at hs
  simpa only [he] using hs

variable {Z : Type*} [AddCommGroup Z] [Module (ZMod 2) Z]

/-- If a point is missed, its Fourier inversion sum vanishes. No division is used. -/
theorem missing_point_fourier [Fintype V] [Fintype (Module.Dual (ZMod 2) Z)]
    (Q : V → Z) (t : Z) (ht : ∀ x, Q x ≠ t) :
    ∑ ell : Module.Dual (ZMod 2) Z,
      sign (ell t) * (∑ x, sign (ell (Q x))) = 0 := by
  classical
  simp_rw [Finset.mul_sum, ← sign_sub, ← map_sub]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro x _
  rw [sum_sign_dual]
  exact if_neg (sub_ne_zero.mpr (Ne.symm (ht x)))

end Kourovka2135.BinaryFourier
