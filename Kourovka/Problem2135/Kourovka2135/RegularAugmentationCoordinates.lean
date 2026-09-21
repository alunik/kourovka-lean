import Kourovka2135.RegularAugmentationIrreducible
import Mathlib.LinearAlgebra.Finsupp.Pi

/-! Restricting the actual augmentation module to a subgroup regular away
from one fixed point gives its actual left regular representation. The
coordinates evaluate on the regular orbit; the omitted coordinate is minus
their sum. This statement works in every characteristic. -/

set_option autoImplicit false
noncomputable section
universe u
namespace Kourovka2135
namespace RegularAugmentationCoordinates

open FinitePermutationAugmentation RegularAugmentationIrreducible
open scoped MonoidAlgebra

variable (k G X : Type u) [Field k] [Group G] [Fintype X] [MulAction G X]
variable (U : Subgroup G) [Fintype U] (x₀ : X)
variable (hfix : ∀ u : U, (u : G) • x₀ = x₀)
variable (hregular : ∀ x y : X, x ≠ x₀ → y ≠ x₀ → ∃! u : U, (u : G) • x = y)
variable (x₁ : X) (hx₁ : x₁ ≠ x₀)

/-- Actual values on the regular orbit. -/
def coordinates : Space k X →ₗ[k] (U → k) where
  toFun f a := (f : X → k) ((a : G) • x₁)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

include hfix hregular hx₁ in
theorem coordinates_injective : Function.Injective (coordinates k G X U x₁) := by
  apply (LinearMap.ker_eq_bot).mp
  apply LinearMap.ker_eq_bot'.mpr
  intro f hf
  have horbit (a : U) : (f : X → k) ((a : G) • x₁) = 0 := congrFun hf a
  have hsum := sum_orbit_add U x₀ hfix hregular x₁ hx₁ (f : X → k)
  have hz : (∑ x : X, (f : X → k) x) = 0 := f.property
  have hbase : (f : X → k) x₀ = 0 := by
    simpa [horbit, hz] using hsum
  apply Subtype.ext
  funext x
  by_cases hx : x = x₀
  · simpa [hx] using hbase
  · obtain ⟨a, ha, _⟩ := hregular x₁ x hx₁ hx
    rw [← ha]
    exact horbit a

include hfix hregular hx₁ in
theorem coordinates_surjective : Function.Surjective (coordinates k G X U x₁) := by
  classical
  intro v
  let e := orbitSumEquiv U x₀ hfix hregular x₁ hx₁
  let f : X → k := fun x => Sum.elim v (fun _ => -∑ a : U, v a) (e.symm x)
  have hf : augmentation k X f = 0 := by
    change (∑ x : X, f x) = 0
    rw [← e.sum_comp f]
    simp [f, Fintype.sum_sum_type]
  refine ⟨⟨f, hf⟩, ?_⟩
  funext a
  change f (e (Sum.inl a)) = v a
  simp [f]

/-- The genuine linear coordinate isomorphism, not merely a dimension count. -/
def coordinateEquiv : Space k X ≃ₗ[k] (U → k) :=
  LinearEquiv.ofBijective (coordinates k G X U x₁)
    ⟨coordinates_injective k G X U x₀ hfix hregular x₁ hx₁,
      coordinates_surjective k G X U x₀ hfix hregular x₁ hx₁⟩

omit [Fintype U] in
theorem coordinates_action (g : U) (f : Space k X) :
    coordinates k G X U x₁ (action k G X (g : G) f) =
      FinitePermutationAugmentation.representation k U U g (coordinates k G X U x₁ f) := by
  funext a
  change (f : X → k) ((g : G)⁻¹ • ((a : G) • x₁)) =
    (f : X → k) (((g⁻¹ * a : U) : G) • x₁)
  rw [← mul_smul]
  rfl

/-- The subgroup acts by actual left translation on the coordinate index. -/
def functionRegularEquiv :
    Representation.Equiv ((action k G X).comp U.subtype)
      (FinitePermutationAugmentation.representation k U U) :=
  Representation.Equiv.mk (coordinateEquiv k G X U x₀ hfix hregular x₁ hx₁) (by
    intro g
    apply LinearMap.ext
    intro f
    exact coordinates_action k G X U x₁ g f)

end RegularAugmentationCoordinates

namespace RegularFunctionRepresentation
open scoped MonoidAlgebra
variable (k H : Type u) [Field k] [Group H] [Fintype H]

/-- Standard coefficient coordinates on the actual group algebra. -/
def coordinates : k[H] ≃ₗ[k] (H → k) :=
  (MonoidAlgebra.coeffLinearEquiv k).trans (Finsupp.linearEquivFunOnFinite k k H)

omit [Group H] in
@[simp] theorem coordinates_apply (f : k[H]) (h : H) : coordinates k H f h = f.coeff h := rfl

def equiv : (Representation.leftRegular k H).Equiv
    (FinitePermutationAugmentation.representation k H H) :=
  Representation.Equiv.mk (coordinates k H) (by
    intro g
    apply LinearMap.ext
    intro f
    funext h
    change (Representation.leftRegular k H g f).coeff h = f.coeff (g⁻¹ * h)
    exact Representation.coeff_ofMulAction g f h)

end RegularFunctionRepresentation

namespace RegularAugmentationCoordinates
open FinitePermutationAugmentation

variable (k G X : Type u) [Field k] [Group G] [Fintype X] [MulAction G X]
variable (U : Subgroup G) [Fintype U] (x₀ : X)
variable (hfix : ∀ u : U, (u : G) • x₀ = x₀)
variable (hregular : ∀ x y : X, x ≠ x₀ → y ≠ x₀ → ∃! u : U, (u : G) • x = y)
variable (x₁ : X) (hx₁ : x₁ ≠ x₀)

/-- Exact restriction to the genuine group-algebra left regular module. -/
def regularEquiv : Representation.Equiv ((action k G X).comp U.subtype)
    (Representation.leftRegular k U) :=
  (functionRegularEquiv k G X U x₀ hfix hregular x₁ hx₁).trans
    (RegularFunctionRepresentation.equiv k U).symm

include hfix hregular hx₁ in
theorem finrank_space : Module.finrank k (Space k X) = Fintype.card U := by
  rw [(coordinateEquiv k G X U x₀ hfix hregular x₁ hx₁).finrank_eq]
  simp

end RegularAugmentationCoordinates
end Kourovka2135
