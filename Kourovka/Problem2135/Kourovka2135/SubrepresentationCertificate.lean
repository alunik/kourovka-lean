import Mathlib.RepresentationTheory.Basic
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Algebra.Group.Subgroup.Lattice

/-! An injective finite-generator intertwiner constructs a genuine
subrepresentation of an existing group representation. Invertible generator
operators certify invariance; no presentation or exactness assertion is assumed. -/

set_option autoImplicit false
noncomputable section
namespace Kourovka2135.SubrepresentationCertificate
variable {k G V W : Type*} [CommRing k] [Group G]
variable [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
variable (ρ : Representation k G V) (K : W →ₗ[k] V)

def compatibleSubgroup : Subgroup G where
  carrier := {g | ∃ A : W ≃ₗ[k] W, ∀ w, ρ g (K w) = K (A w)}
  one_mem' := by refine ⟨1, ?_⟩; intro w; simp
  mul_mem' := by
    rintro g h ⟨A, hA⟩ ⟨B, hB⟩
    refine ⟨A * B, ?_⟩
    intro w
    rw [map_mul, Module.End.mul_apply, hB, hA]
    rfl
  inv_mem' := by
    rintro g ⟨A, hA⟩
    refine ⟨A.symm, ?_⟩
    intro w
    apply (ρ.apply_bijective g).injective
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    simpa using (hA (A.symm w)).symm

theorem range_invariant (s : Set G) (hs : Subgroup.closure s = ⊤)
    (hedge : ∀ g ∈ s, ∃ A : W ≃ₗ[k] W, ∀ w, ρ g (K w) = K (A w)) :
    ∀ g, LinearMap.range K ≤ (LinearMap.range K).comap (ρ g) := by
  have h : Subgroup.closure s ≤ compatibleSubgroup ρ K := (Subgroup.closure_le _).mpr hedge
  rw [hs] at h
  intro g v hv
  obtain ⟨w, rfl⟩ := hv
  obtain ⟨A, hA⟩ := h (Subgroup.mem_top g)
  exact ⟨A w, (hA w).symm⟩

/-- Restrict the actual action to the certified image and use the given coordinates. -/
def representation (hK : Function.Injective K)
    (s : Set G) (hs : Subgroup.closure s = ⊤)
    (hedge : ∀ g ∈ s, ∃ A : W ≃ₗ[k] W, ∀ w, ρ g (K w) = K (A w)) :
    Representation k G W :=
  (LinearEquiv.ofInjective K hK).symm.conjRingEquiv.toMonoidHom.comp
    (ρ.subrepresentation (LinearMap.range K) (range_invariant ρ K s hs hedge))

theorem representation_intertwines (hK : Function.Injective K)
    (s : Set G) (hs : Subgroup.closure s = ⊤)
    (hedge : ∀ g ∈ s, ∃ A : W ≃ₗ[k] W, ∀ w, ρ g (K w) = K (A w))
    (g : G) (w : W) :
    K (representation ρ K hK s hs hedge g w) = ρ g (K w) := by
  change ((LinearEquiv.ofInjective K hK)
    ((LinearEquiv.ofInjective K hK).symm
      ((ρ.subrepresentation (LinearMap.range K) (range_invariant ρ K s hs hedge)) g
        ((LinearEquiv.ofInjective K hK) w)))).val = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

theorem representation_eq_of_intertwines (hK : Function.Injective K)
    (s : Set G) (hs : Subgroup.closure s = ⊤)
    (hedge : ∀ g ∈ s, ∃ A : W ≃ₗ[k] W, ∀ w, ρ g (K w) = K (A w))
    (g : G) (A : W →ₗ[k] W) (hA : ∀ w, ρ g (K w) = K (A w)) :
    representation ρ K hK s hs hedge g = A := by
  ext w
  apply hK
  rw [representation_intertwines, hA]

end Kourovka2135.SubrepresentationCertificate
