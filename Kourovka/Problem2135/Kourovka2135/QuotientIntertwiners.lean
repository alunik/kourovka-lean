import Kourovka2135.MinimalQuotientModules
import Mathlib.RepresentationTheory.Intertwining

/-! Factoring a representation through a quotient does not change its
intertwining endomorphisms. -/

set_option autoImplicit false
universe u v w
namespace Kourovka2135
variable {k : Type u} [CommRing k]
variable {G : Type v} [Group G] {M : Type w} [AddCommGroup M] [Module k M]

def quotientEndomorphismEquiv (ρ : Representation k G M)
    (R : Subgroup G) [R.Normal] (hR : ∀ (r : R) x, ρ (r : G) x = x) :
    (quotientRepresentation ρ R hR).IntertwiningMap (quotientRepresentation ρ R hR) ≃ₗ[k]
      ρ.IntertwiningMap ρ where
  toFun f := ⟨f.toLinearMap, by
    intro g
    exact f.isIntertwining' (QuotientGroup.mk' R g)⟩
  invFun f := ⟨f.toLinearMap, by
    intro g
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective R g
    exact f.isIntertwining' a⟩
  left_inv f := by ext x; rfl
  right_inv f := by ext x; rfl
  map_add' f h := by ext x; rfl
  map_smul' a f := by ext x; rfl

end Kourovka2135
