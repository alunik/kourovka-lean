import Kourovka2135.ScalarPowerAdditivity

/-! Biadditive forms invariant under two full scalar weights vanish when
inverse-power scaling fails additivity. The codomain is an arbitrary abelian
group; no finite-dimensionality, splitting field, or representation theorem
is involved. -/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.ScalarInvariantBiadditive

variable {F A : Type*} [Field F] [AddCommGroup A]

/-- A biadditive invariant form is determined by its values at second input one. -/
theorem value_eq (n : ℕ) (hn : 0 < n) (B : F →+ (F →+ A))
    (hB : ∀ (u : Fˣ) (x y : F), B ((u : F) ^ n * x) ((u : F) * y) = B x y)
    (x y : F) : B x y = B ((y ^ n)⁻¹ * x) 1 := by
  by_cases hy : y = 0
  · subst y
    simp [zero_pow hn.ne']
  · have h := hB (Units.mk0 y hy) ((y ^ n)⁻¹ * x) 1
    simpa only [Units.val_mk0, mul_one, ← mul_assoc,
      mul_inv_cancel₀ (pow_ne_zero n hy), one_mul] using h

/-- Failure of inverse-power additivity annihilates every invariant biadditive form. -/
theorem eq_zero_of_not_additive (n : ℕ) (hn : 0 < n)
    (hbad : ¬ ∀ x y : F, ((x + y) ^ n)⁻¹ = (x ^ n)⁻¹ + (y ^ n)⁻¹)
    (B : F →+ (F →+ A))
    (hB : ∀ (u : Fˣ) (x y : F), B ((u : F) ^ n * x) ((u : F) * y) = B x y) :
    B = 0 := by
  classical
  push Not at hbad
  obtain ⟨y, z, hne⟩ := hbad
  let f : F →+ A :=
    { toFun := fun x => B x 1
      map_zero' := by simp
      map_add' := by intro x y; simp }
  let d : F := ((y + z) ^ n)⁻¹ - ((y ^ n)⁻¹ + (z ^ n)⁻¹)
  have hd : d ≠ 0 := sub_ne_zero.mpr hne
  have hv (x t : F) : B x t = f ((t ^ n)⁻¹ * x) := value_eq n hn B hB x t
  have he (x : F) : f (((y + z) ^ n)⁻¹ * x) =
      f (((y ^ n)⁻¹ + (z ^ n)⁻¹) * x) := by
    rw [add_mul, map_add, ← hv, ← hv, ← hv]
    exact (B x).map_add y z
  have hk (x : F) : f (d * x) = 0 := by
    change f ((((y + z) ^ n)⁻¹ - ((y ^ n)⁻¹ + (z ^ n)⁻¹)) * x) = 0
    rw [sub_mul, map_sub, he, sub_self]
  have hf (x : F) : f x = 0 := by
    simpa only [← mul_assoc, mul_inv_cancel₀ hd, one_mul] using hk (d⁻¹ * x)
  apply AddMonoidHom.ext
  intro x
  apply AddMonoidHom.ext
  intro t
  change B x t = 0
  rw [hv, hf]

/-- The polynomial root-count obstruction gives a concrete finite binary-field gate. -/
theorem eq_zero_of_card [Finite F] [CharP F 2] (n : ℕ) (hn : 0 < n)
    (hcard : 2 * n + 2 < Nat.card F) (B : F →+ (F →+ A))
    (hB : ∀ (u : Fˣ) (x y : F), B ((u : F) ^ n * x) ((u : F) * y) = B x y) :
    B = 0 :=
  eq_zero_of_not_additive n hn
    (ScalarPowerAdditivity.inverse_power_not_additive n hn hcard) B hB

end Kourovka2135.ScalarInvariantBiadditive
