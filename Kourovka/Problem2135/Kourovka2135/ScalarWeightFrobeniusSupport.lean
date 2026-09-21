import Kourovka2135.ScalarWeightAdditiveMaps
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Algebra.Algebra.ZMod

/-! A nonzero full-weight additive map, normalized at one, is a field
homomorphism. Over a finite binary field its weight is therefore an actual
Frobenius power. No list of additive maps or characters is assumed. -/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.ScalarWeightFrobeniusSupport

open ScalarWeightAdditiveMaps

variable {F k : Type*} [Field F] [Field k]

/-- Normalization at one turns a nonzero weight vector into a field map. -/
def normalizedHom (χ : Fˣ →* kˣ) (f : weightSpace χ)
    (hf : f.val 1 ≠ 0) : F →+* k where
  toFun x := f.val x / f.val 1
  map_zero' := by simp
  map_one' := div_self hf
  map_add' x y := by rw [map_add, add_div]
  map_mul' x y := by
    by_cases hx : x = 0
    · simp [hx]
    · let u : Fˣ := Units.mk0 x hx
      have hxy := f.property u y
      have hx1 := f.property u 1
      change f.val (x * y) = (χ u : k) * f.val y at hxy
      change f.val (x * 1) = (χ u : k) * f.val 1 at hx1
      rw [mul_one] at hx1
      rw [hxy, hx1]
      field_simp

theorem normalizedHom_units (χ : Fˣ →* kˣ) (f : weightSpace χ)
    (hf : f.val 1 ≠ 0) (u : Fˣ) :
    normalizedHom χ f hf (u : F) = (χ u : k) := by
  have h := f.property u 1
  simp only [mul_one] at h
  change f.val (u : F) / f.val 1 = _
  rw [h, mul_div_cancel_right₀ _ hf]

/-- Every binary finite-field endomorphism is one of its Frobenius iterates. -/
theorem ringHom_eq_frobenius [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    (g : F →+* F) :
    ∃ j : Fin (Module.finrank (ZMod 2) F), ∀ x : F, g x = x ^ (2 ^ j.val) := by
  let a : F →ₐ[ZMod 2] F :=
    { g with
      commutes' := by
        intro x
        exact DFunLike.congr_fun
          (Subsingleton.elim (g.comp (algebraMap (ZMod 2) F)) (algebraMap (ZMod 2) F)) x }
  obtain ⟨j, hj⟩ := (FiniteField.bijective_frobeniusAlgHom_pow (ZMod 2) F).surjective a
  refine ⟨j, fun x => ?_⟩
  have h := DFunLike.congr_fun hj x
  simpa only [AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom, ZMod.card,
    pow_iterate, AlgHom.one_apply, a, AlgHom.coe_mk] using h.symm

/-- The character of a nonzero weight vector is an actual Frobenius power. -/
theorem character_eq_frobenius [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    (χ : Fˣ →* Fˣ) (f : weightSpace χ) (hf : f ≠ 0) :
    ∃ j : Fin (Module.finrank (ZMod 2) F),
      ∀ u : Fˣ, (χ u : F) = (u : F) ^ (2 ^ j.val) := by
  have h1 : f.val 1 ≠ 0 := by
    intro h
    apply hf
    apply evaluation_injective χ
    exact h.trans (map_zero (evaluation χ)).symm
  obtain ⟨j, hj⟩ := ringHom_eq_frobenius (normalizedHom χ f h1)
  exact ⟨j, fun u => (normalizedHom_units χ f h1 u).symm.trans (hj u)⟩

/-- Missing Frobenius support annihilates the actual additive weight space. -/
theorem weightSpace_subsingleton [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    (χ : Fˣ →* Fˣ)
    (hχ : ¬ ∃ j : Fin (Module.finrank (ZMod 2) F),
      ∀ u : Fˣ, (χ u : F) = (u : F) ^ (2 ^ j.val)) :
    Subsingleton (weightSpace χ) := by
  refine ⟨fun f g => ?_⟩
  have hz : ∀ f : weightSpace χ, f = 0 := by
    intro f
    by_contra hf
    exact hχ (character_eq_frobenius χ f hf)
  rw [hz f, hz g]

end Kourovka2135.ScalarWeightFrobeniusSupport
