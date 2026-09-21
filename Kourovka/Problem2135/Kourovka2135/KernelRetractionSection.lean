import Mathlib.Algebra.Group.Subgroup.Ker

/-! A retraction onto the actual kernel constructs a section of a surjective
group homomorphism. The section fixes every lift killed by the retraction.
No finiteness, centrality, representation, or classification premise is needed.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.KernelRetractionSection

universe u v
variable {H : Type u} {G : Type v} [Group H] [Group G]
variable (π : H →* G) (κ : H →* π.ker)
variable (hκ : ∀ k : π.ker, κ (k : H) = k)

/-- Restrict the original projection to the retraction kernel. -/
def restriction : κ.ker →* G := π.comp κ.ker.subtype

include hκ in
/-- A kernel retraction makes the restricted projection injective. -/
theorem restriction_injective : Function.Injective (restriction π κ) := by
  apply (MonoidHom.ker_eq_bot_iff (restriction π κ)).mp
  apply le_antisymm ?_ bot_le
  intro x hx
  apply Subgroup.mem_bot.mpr
  apply Subtype.ext
  have hp : π (x : H) = 1 := hx
  let z : π.ker := ⟨(x : H), hp⟩
  have hz : z = 1 := by
    rw [← hκ z]
    exact x.property
  exact congrArg (fun a : π.ker => (a : H)) hz

include hκ in
/-- Correct any preimage by its actual kernel coordinate. -/
theorem restriction_surjective (hπ : Function.Surjective π) :
    Function.Surjective (restriction π κ) := by
  intro g
  obtain ⟨h, hh⟩ := hπ g
  let z : H := ((κ h : π.ker) : H)⁻¹ * h
  have hz : z ∈ κ.ker := by
    apply MonoidHom.mem_ker.mpr
    dsimp only [z]
    rw [map_mul, map_inv, hκ (κ h), inv_mul_cancel]
  refine ⟨⟨z, hz⟩, ?_⟩
  change π (((κ h : π.ker) : H)⁻¹ * h) = g
  rw [map_mul, map_inv, MonoidHom.mem_ker.mp (κ h).property, inv_one, one_mul, hh]

/-- The actual restriction isomorphism. -/
def restrictionEquiv (hπ : Function.Surjective π) : κ.ker ≃* G :=
  MulEquiv.ofBijective (restriction π κ)
    ⟨restriction_injective π κ hκ, restriction_surjective π κ hκ hπ⟩

/-- The inverse restricted projection, included in the original group. -/
def sectionHom (hπ : Function.Surjective π) : G →* H :=
  κ.ker.subtype.comp (restrictionEquiv π κ hκ hπ).symm.toMonoidHom

@[simp] theorem projection_section (hπ : Function.Surjective π) (g : G) :
    π (sectionHom π κ hκ hπ g) = g :=
  (restrictionEquiv π κ hκ hπ).apply_symm_apply g

theorem projection_comp_section (hπ : Function.Surjective π) :
    π.comp (sectionHom π κ hκ hπ) = MonoidHom.id G := by
  apply MonoidHom.ext
  exact projection_section π κ hκ hπ

/-- Every lift with trivial retraction coordinate is preserved exactly. -/
theorem section_projection_of_retraction_eq_one (hπ : Function.Surjective π)
    (h : H) (hh : κ h = 1) : sectionHom π κ hκ hπ (π h) = h := by
  let x : κ.ker := ⟨h, hh⟩
  exact congrArg Subtype.val ((restrictionEquiv π κ hκ hπ).symm_apply_apply x)

end Kourovka2135.KernelRetractionSection
