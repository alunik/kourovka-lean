import Mathlib.RepresentationTheory.Basic
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Algebra.Group.Subgroup.Lattice

/-! A surjective generator intertwiner constructs a genuine quotient
representation. The candidate operators on the quotient need only be
specified at a generating set, as actual linear equivalences. There is no
assumed all-group homomorphism, presentation, finiteness or semisimplicity. -/

set_option autoImplicit false
noncomputable section
namespace Kourovka2135.QuotientRepresentationCertificate

variable {k G V W : Type*} [CommRing k] [Group G]
variable [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
variable (ρ : Representation k G V) (C : V →ₗ[k] W)

/-- Elements whose action has an actual invertible operator on the proposed quotient. -/
def compatibleSubgroup : Subgroup G where
  carrier := {g | ∃ A : W ≃ₗ[k] W, ∀ v, C (ρ g v) = A (C v)}
  one_mem' := by
    refine ⟨1, ?_⟩
    intro v
    simp
  mul_mem' := by
    rintro g h ⟨A, hA⟩ ⟨B, hB⟩
    refine ⟨A * B, ?_⟩
    intro v
    change C ((ρ (g * h)) v) = A (B (C v))
    rw [map_mul, Module.End.mul_apply, hA, hB]
  inv_mem' := by
    rintro g ⟨A, hA⟩
    refine ⟨A.symm, ?_⟩
    intro v
    apply A.injective
    rw [A.apply_symm_apply]
    have h := hA (ρ g⁻¹ v)
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at h
    exact h.symm

/-- The two finite generator equations suffice for invariant kernel on the entire group. -/
theorem kernel_invariant (s : Set G) (hs : Subgroup.closure s = ⊤)
    (hedge : ∀ g ∈ s, ∃ A : W ≃ₗ[k] W, ∀ v, C (ρ g v) = A (C v)) :
    ∀ g, LinearMap.ker C ≤ (LinearMap.ker C).comap (ρ g) := by
  have hk : Subgroup.closure s ≤ compatibleSubgroup ρ C :=
    (Subgroup.closure_le _).mpr hedge
  rw [hs] at hk
  intro g v hv
  obtain ⟨A, hA⟩ := hk (Subgroup.mem_top g)
  change C (ρ g v) = 0
  rw [hA, show C v = 0 from hv, map_zero]

/-- The actual quotient action transported to the supplied target space. -/
def representation (hC : Function.Surjective C)
    (s : Set G) (hs : Subgroup.closure s = ⊤)
    (hedge : ∀ g ∈ s, ∃ A : W ≃ₗ[k] W, ∀ v, C (ρ g v) = A (C v)) :
    Representation k G W :=
  (C.quotKerEquivOfSurjective hC).conjRingEquiv.toMonoidHom.comp
    (ρ.quotient (LinearMap.ker C) (kernel_invariant ρ C s hs hedge))

/-- C intertwines the newly constructed representation on every actual group element. -/
theorem representation_apply_image (hC : Function.Surjective C)
    (s : Set G) (hs : Subgroup.closure s = ⊤)
    (hedge : ∀ g ∈ s, ∃ A : W ≃ₗ[k] W, ∀ v, C (ρ g v) = A (C v))
    (g : G) (v : V) :
    representation ρ C hC s hs hedge g (C v) = C (ρ g v) := by
  change (C.quotKerEquivOfSurjective hC)
    ((ρ.quotient (LinearMap.ker C) (kernel_invariant ρ C s hs hedge)) g
      ((C.quotKerEquivOfSurjective hC).symm (C v))) = _
  rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
  rfl

/-- A supplied candidate generator operator is the actual operator of the constructed action. -/
theorem representation_eq_of_intertwines (hC : Function.Surjective C)
    (s : Set G) (hs : Subgroup.closure s = ⊤)
    (hedge : ∀ g ∈ s, ∃ A : W ≃ₗ[k] W, ∀ v, C (ρ g v) = A (C v))
    (g : G) (A : W →ₗ[k] W) (hA : ∀ v, C (ρ g v) = A (C v)) :
    representation ρ C hC s hs hedge g = A := by
  ext w
  obtain ⟨v, rfl⟩ := hC w
  rw [representation_apply_image, hA]

end Kourovka2135.QuotientRepresentationCertificate
