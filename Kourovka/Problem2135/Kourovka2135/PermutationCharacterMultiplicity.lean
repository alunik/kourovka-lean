import Kourovka2135.WeightedCharacterProjector
import Kourovka2135.FinitePermutationHeart
import Kourovka2135.MultiplicityOneIntertwining

/-! A nontrivial character occurs at most once in a permutation augmentation
module with one fixed point and one remaining orbit. Evaluation at a point of
the second orbit injects the actual weighted-projector range into the ground
field. The actual augmentation-to-heart quotient maps this range onto the
corresponding heart range. No Fourier basis, semisimplicity, or irreducibility
is assumed, and the rank bounds do not require the subgroup order to be
invertible (the weighted operator may then be zero).
-/

set_option autoImplicit false
noncomputable section
universe u

namespace Kourovka2135.PermutationCharacterMultiplicity

open FinitePermutationAugmentation
open scoped MonoidAlgebra

variable (k G X : Type u) [Field k] [Group G] [Fintype X] [MulAction G X]
variable (U : Subgroup G) [Fintype U] (χ : U →* kˣ)

def augmentationProjector : Space k X →ₗ[k] Space k X :=
  WeightedCharacterProjector.projector ((action k G X).comp U.subtype) χ

/-- The actual range consists of vectors with the prescribed character. -/
theorem range_eigenvalue (f : LinearMap.range (augmentationProjector k G X U χ))
    (g : U) :
    action k G X (g : G) f.val = (χ g : k) • f.val := by
  obtain ⟨v, hv⟩ := f.property
  rw [← hv]
  exact WeightedCharacterProjector.action_projector
    ((action k G X).comp U.subtype) χ g v

theorem range_eigenvalue_apply
    (f : LinearMap.range (augmentationProjector k G X U χ)) (g : U) (x : X) :
    (f.val : X → k) ((g : G)⁻¹ • x) = (χ g : k) * (f.val : X → k) x := by
  exact congrArg (fun v : Space k X => (v : X → k) x)
    (range_eigenvalue k G X U χ f g)

/-- Nontriviality of the character kills the fixed-point coordinate. -/
theorem range_basePoint_zero (x₀ : X) (hχ : χ ≠ 1)
    (hfix : U ≤ MulAction.stabilizer G x₀)
    (f : LinearMap.range (augmentationProjector k G X U χ)) :
    (f.val : X → k) x₀ = 0 := by
  have hex : ∃ g : U, χ g ≠ 1 := by
    by_contra hn
    apply hχ
    apply MonoidHom.ext
    intro g
    by_contra hg
    exact hn ⟨g, hg⟩
  obtain ⟨g, hg⟩ := hex
  have hfixed : (g : G)⁻¹ • x₀ = x₀ := hfix (g⁻¹).property
  have he := range_eigenvalue_apply k G X U χ f g x₀
  rw [hfixed] at he
  by_contra hnonzero
  apply hg
  apply Units.ext
  exact (mul_eq_right₀ hnonzero).mp he.symm

/-- Evaluate the actual range at one point of the nontrivial orbit. -/
def rangeEvaluation (x₁ : X) :
    LinearMap.range (augmentationProjector k G X U χ) →ₗ[k] k where
  toFun f := (f.val : X → k) x₁
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem rangeEvaluation_injective (x₀ x₁ : X) (hχ : χ ≠ 1)
    (hfix : U ≤ MulAction.stabilizer G x₀) (hx₁ : x₁ ≠ x₀)
    (htrans : ∀ x y : X, x ≠ x₀ → y ≠ x₀ → ∃ g : U, (g : G) • x = y) :
    Function.Injective (rangeEvaluation k G X U χ x₁) := by
  intro f h he
  change (f.val : X → k) x₁ = (h.val : X → k) x₁ at he
  apply Subtype.ext
  apply Subtype.ext
  funext x
  by_cases hx : x = x₀
  · subst x
    rw [range_basePoint_zero k G X U χ x₀ hχ hfix f,
      range_basePoint_zero k G X U χ x₀ hχ hfix h]
  · obtain ⟨g, hg⟩ := htrans x₁ x hx₁ hx
    have hf : (f.val : X → k) x = (χ g⁻¹ : k) * (f.val : X → k) x₁ := by
      simpa only [InvMemClass.coe_inv, inv_inv, hg] using
        range_eigenvalue_apply k G X U χ f g⁻¹ x₁
    have hh : (h.val : X → k) x = (χ g⁻¹ : k) * (h.val : X → k) x₁ := by
      simpa only [InvMemClass.coe_inv, inv_inv, hg] using
        range_eigenvalue_apply k G X U χ h g⁻¹ x₁
    exact hf.trans ((congrArg (fun c : k => (χ g⁻¹ : k) * c) he).trans hh.symm)

/-- A single actual evaluation bounds the weighted augmentation range by one. -/
theorem augmentationProjector_finrank_le_one (x₀ x₁ : X) (hχ : χ ≠ 1)
    (hfix : U ≤ MulAction.stabilizer G x₀) (hx₁ : x₁ ≠ x₀)
    (htrans : ∀ x y : X, x ≠ x₀ → y ≠ x₀ → ∃ g : U, (g : G) • x = y) :
    Module.finrank k (LinearMap.range (augmentationProjector k G X U χ)) ≤ 1 := by
  have h := LinearMap.finrank_le_finrank_of_injective
    (f := rangeEvaluation k G X U χ x₁)
    (rangeEvaluation_injective k G X U χ x₀ x₁ hχ hfix hx₁ htrans)
  simpa only [CommSemiring.finrank_self] using h

/-- The same rank bound for the explicit ambient group-algebra element. -/
theorem augmentation_element_finrank_le_one (x₀ x₁ : X) (hχ : χ ≠ 1)
    (hfix : U ≤ MulAction.stabilizer G x₀) (hx₁ : x₁ ≠ x₀)
    (htrans : ∀ x y : X, x ≠ x₀ → y ≠ x₀ → ∃ g : U, (g : G) • x = y) :
    Module.finrank k (LinearMap.range
      ((action k G X).asAlgebraHom (WeightedCharacterProjector.element χ U.subtype))) ≤ 1 := by
  rw [WeightedCharacterProjector.asAlgebraHom_element]
  exact augmentationProjector_finrank_le_one k G X U χ x₀ x₁ hχ hfix hx₁ htrans

/-- The actual heart quotient preserves the rank-one bound by range surjectivity. -/
theorem heart_element_finrank_le_one (hcard : (Fintype.card X : k) = 0)
    (x₀ x₁ : X) (hχ : χ ≠ 1)
    (hfix : U ≤ MulAction.stabilizer G x₀) (hx₁ : x₁ ≠ x₀)
    (htrans : ∀ x y : X, x ≠ x₀ → y ≠ x₀ → ∃ g : U, (g : G) • x = y) :
    Module.finrank k (LinearMap.range
      ((FinitePermutationHeart.representation k G X hcard).asAlgebraHom
        (WeightedCharacterProjector.element χ U.subtype))) ≤ 1 := by
  let ρ := action k G X
  let τ := FinitePermutationHeart.representation k G X hcard
  let a : k[G] := WeightedCharacterProjector.element χ U.subtype
  let f : ρ.IntertwiningMap τ := FinitePermutationHeart.quotientHom k G X hcard
  have hcomm := MultiplicityOneIntertwining.intertwining_asAlgebraHom ρ τ a
  have hsurj := MultiplicityOneIntertwining.rangeRestriction_surjective
    ρ τ (ρ.asAlgebraHom a) (τ.asAlgebraHom a) hcomm f
    (FinitePermutationHeart.quotientHom_surjective k G X hcard)
  have hdim := LinearMap.finrank_le_finrank_of_surjective
    (f := MultiplicityOneIntertwining.rangeRestriction
      ρ τ (ρ.asAlgebraHom a) (τ.asAlgebraHom a) hcomm f) hsurj
  exact hdim.trans (augmentation_element_finrank_le_one
    k G X U χ x₀ x₁ hχ hfix hx₁ htrans)

theorem heart_projector_finrank_le_one (hcard : (Fintype.card X : k) = 0)
    (x₀ x₁ : X) (hχ : χ ≠ 1)
    (hfix : U ≤ MulAction.stabilizer G x₀) (hx₁ : x₁ ≠ x₀)
    (htrans : ∀ x y : X, x ≠ x₀ → y ≠ x₀ → ∃ g : U, (g : G) • x = y) :
    Module.finrank k (LinearMap.range (WeightedCharacterProjector.projector
      ((FinitePermutationHeart.representation k G X hcard).comp U.subtype) χ)) ≤ 1 := by
  rw [← WeightedCharacterProjector.asAlgebraHom_element]
  exact heart_element_finrank_le_one k G X U χ hcard x₀ x₁ hχ hfix hx₁ htrans

end Kourovka2135.PermutationCharacterMultiplicity
