import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.Module.Hom
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Additive maps with a full multiplicative-field weight.

Every such map is determined by its value at one. A nonzero map forces the
zero-extended weight function to be additive, so a concrete failure of that
identity proves vanishing. This is a generic calculation, not a Suzuki H1
value or an assumed description of the Suzuki root abelianization.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.ScalarWeightAdditiveMaps

variable {F k : Type*} [Field F] [Field k]

/-- Actual additive maps transforming by the specified multiplicative weight. -/
def weightSpace (χ : Fˣ →* kˣ) : Submodule k (F →+ k) where
  carrier := {f | ∀ (t : Fˣ) (x : F), f ((t : F) * x) = (χ t : k) * f x}
  zero_mem' := by intro t x; simp
  add_mem' := by
    intro f g hf hg t x
    change f ((t : F) * x) + g ((t : F) * x) = (χ t : k) * (f x + g x)
    rw [hf, hg, mul_add]
  smul_mem' := by
    intro a f hf t x
    change a * f ((t : F) * x) = (χ t : k) * (a * f x)
    rw [hf]
    ring

/-- The one-coordinate evaluation map, with the actual target scalar structure. -/
def evaluation (χ : Fˣ →* kˣ) : weightSpace χ →ₗ[k] k where
  toFun f := f.val 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Nonzero field elements are all scalar translates of one. -/
theorem evaluation_injective (χ : Fˣ →* kˣ) : Function.Injective (evaluation χ) := by
  intro f g h
  apply Subtype.ext
  apply AddMonoidHom.ext
  intro x
  by_cases hx : x = 0
  · simp [hx]
  · let t : Fˣ := Units.mk0 x hx
    have hf := f.property t 1
    have hg := g.property t 1
    change f.val 1 = g.val 1 at h
    simp only [mul_one] at hf hg
    exact hf.trans ((congrArg (fun z : k => (χ t : k) * z) h).trans hg.symm)

/-- The full-weight additive map space really is finite-dimensional. -/
theorem finiteDimensional_weightSpace (χ : Fˣ →* kˣ) :
    FiniteDimensional k (weightSpace χ) :=
  FiniteDimensional.of_injective (evaluation χ) (evaluation_injective χ)

theorem finrank_weightSpace_le_one (χ : Fˣ →* kˣ) :
    Module.finrank k (weightSpace χ) ≤ 1 := by
  simpa using LinearMap.finrank_le_finrank_of_injective (evaluation_injective χ)

/-- Recover all values from the extension of the character by zero. -/
theorem value_eq (χ : Fˣ →* kˣ) (w : F → k) (hw0 : w 0 = 0)
    (hw : ∀ t : Fˣ, w (t : F) = (χ t : k)) (f : weightSpace χ) (x : F) :
    f.val x = w x * f.val 1 := by
  by_cases hx : x = 0
  · simp [hx, hw0]
  · have h := f.property (Units.mk0 x hx) 1
    simpa only [Units.val_mk0, mul_one, ← hw] using h

/-- Any nonzero coordinate forces additivity of the zero-extended weight. -/
theorem additive_of_evaluation_ne_zero (χ : Fˣ →* kˣ)
    (w : F → k) (hw0 : w 0 = 0) (hw : ∀ t : Fˣ, w (t : F) = (χ t : k))
    (f : weightSpace χ) (hf : evaluation χ f ≠ 0) :
    ∀ x y, w (x + y) = w x + w y := by
  intro x y
  apply mul_right_cancel₀ hf
  change w (x + y) * f.val 1 = (w x + w y) * f.val 1
  rw [← value_eq χ w hw0 hw f, add_mul,
    ← value_eq χ w hw0 hw f, ← value_eq χ w hw0 hw f, map_add]

/-- A concrete nonadditivity witness annihilates the entire weight space. -/
theorem weightSpace_eq_bot_of_not_additive (χ : Fˣ →* kˣ)
    (w : F → k) (hw0 : w 0 = 0) (hw : ∀ t : Fˣ, w (t : F) = (χ t : k))
    (hbad : ¬ ∀ x y, w (x + y) = w x + w y) : weightSpace χ = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro f hf
  change f = 0
  have he : evaluation χ ⟨f, hf⟩ = 0 := by
    by_contra hn
    exact hbad (additive_of_evaluation_ne_zero χ w hw0 hw ⟨f, hf⟩ hn)
  have hz : (⟨f, hf⟩ : weightSpace χ) = 0 :=
    evaluation_injective χ (he.trans (map_zero (evaluation χ)).symm)
  exact congrArg Subtype.val hz

/-- The Tits norm is onto by an explicit inverse, without a cyclic-unit or
finite-field theorem. This makes every central root coordinate a square. -/
theorem titsNorm_surjective (θ : F ≃+* F) (hθ : ∀ x, θ (θ x) = x ^ 2) :
    Function.Surjective (fun a : F => a * θ a) := by
  intro b
  by_cases hb : b = 0
  · subst b
    exact ⟨0, by simp⟩
  · refine ⟨θ b / b, ?_⟩
    have hθb : θ b ≠ 0 := (map_ne_zero θ).mpr hb
    change (θ b / b) * θ (θ b / b) = b
    rw [map_div₀, hθ]
    field_simp [hb, hθb]

end Kourovka2135.ScalarWeightAdditiveMaps
