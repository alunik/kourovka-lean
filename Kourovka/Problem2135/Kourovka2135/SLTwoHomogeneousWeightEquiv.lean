import Kourovka2135.SLTwoHomogeneousFunctions
import Mathlib.RepresentationTheory.Intertwining
import Mathlib.FieldTheory.Finite.Basic

/-! Identity-on-functions equivalences between homogeneous weights.

Only equality of the actual unit characters is needed. In particular, over a
finite parameter field, weight `card F - 1` and weight zero define equivalent
SL2 representations by leaving every underlying function unchanged.
-/

set_option autoImplicit false
noncomputable section
universe u v

namespace Kourovka2135.SLTwoHomogeneousWeightEquiv

open SLTwoHomogeneousFunctions

section General
variable (k : Type u) [Field k] {F : Type v} [Field F] (σ : F →+* k)
variable (n m : ℕ) (hpow : ∀ a : Fˣ, σ (a : F) ^ n = σ (a : F) ^ m)

/-- Changing equal unit characters leaves the underlying homogeneous function unchanged. -/
def linearEquiv : Carrier k σ n ≃ₗ[k] Carrier k σ m where
  toFun h := ⟨h.val, by
    intro a z
    rw [← hpow a]
    exact h.property a z⟩
  invFun h := ⟨h.val, by
    intro a z
    rw [hpow a]
    exact h.property a z⟩
  left_inv h := by apply Subtype.ext; rfl
  right_inv h := by apply Subtype.ext; rfl
  map_add' h h' := by apply Subtype.ext; rfl
  map_smul' c h := by apply Subtype.ext; rfl

@[simp] theorem linearEquiv_apply (h : Carrier k σ n) (z : Point F) :
    linearEquiv k σ n m hpow h z = h z := rfl

@[simp] theorem linearEquiv_symm_apply (h : Carrier k σ m) (z : Point F) :
    (linearEquiv k σ n m hpow).symm h z = h z := rfl

/-- The identity on functions intertwines the actual transpose-precomposition action. -/
def equiv : Representation.Equiv (representation k σ n) (representation k σ m) :=
  Representation.Equiv.mk (linearEquiv k σ n m hpow) (by
    intro g
    apply LinearMap.ext
    intro h
    apply Subtype.ext
    rfl)

@[simp] theorem equiv_apply (h : Carrier k σ n) (z : Point F) :
    equiv k σ n m hpow h z = h z := rfl

@[simp] theorem equiv_symm_apply (h : Carrier k σ m) (z : Point F) :
    (equiv k σ n m hpow).symm h z = h z := rfl

/-- The projective coordinates are preserved exactly by the weight equivalence. -/
theorem coordinates_equiv (h : Carrier k σ n) :
    coordinates k σ m (equiv k σ n m hpow h) = coordinates k σ n h := rfl

end General

section Finite
variable (k : Type u) [Field k] {F : Type v} [Field F] [Fintype F] (σ : F →+* k)

/-- The multiplicative-field exponent has the same unit character as zero. -/
theorem unit_pow_card_sub_one (a : Fˣ) :
    σ (a : F) ^ (Fintype.card F - 1) = σ (a : F) ^ 0 := by
  rw [pow_zero, ← map_pow, FiniteField.pow_card_sub_one_eq_one (a : F) a.ne_zero, map_one]

/-- The full multiplicative-field weight is the ordinary projective permutation representation. -/
def cardSubOneEquiv :
    Representation.Equiv (representation k σ (Fintype.card F - 1)) (representation k σ 0) :=
  equiv k σ (Fintype.card F - 1) 0 (unit_pow_card_sub_one k σ)

@[simp] theorem cardSubOneEquiv_apply (h : Carrier k σ (Fintype.card F - 1)) (z : Point F) :
    cardSubOneEquiv k σ h z = h z := rfl

@[simp] theorem cardSubOneEquiv_symm_apply (h : Carrier k σ 0) (z : Point F) :
    (cardSubOneEquiv k σ).symm h z = h z := rfl

end Finite
end Kourovka2135.SLTwoHomogeneousWeightEquiv
