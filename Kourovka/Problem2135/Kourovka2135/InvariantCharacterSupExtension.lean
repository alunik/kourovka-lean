import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Algebra.Group.Subgroup.Pointwise

/-! Extend an actual conjugation-invariant subgroup character to a disjoint
normalizing supplement. The actual semidirect product maps isomorphically to
A ⊔ C, using disjointness and the normalizer product formula. Its lift is
trivial on C and agrees with the original character on A. No finiteness,
order, field, quotient, or assumed complement premise is needed.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.InvariantCharacterSupExtension

open scoped Pointwise

universe u v
variable {G : Type u} [Group G] (A C : Subgroup G)
variable (hnorm : C ≤ Subgroup.normalizer A)

/-- The actual conjugation action of C on A. -/
def action : C →* MulAut A := A.normalizerMonoidHom.comp (Subgroup.inclusion hnorm)

@[simp] theorem action_apply_coe (c : C) (a : A) :
    ((action A C hnorm c a : A) : G) = (c : G) * (a : G) * (c : G)⁻¹ := rfl

/-- Multiply the actual semidirect factors inside their actual subgroup join. -/
def toSup : A ⋊[action A C hnorm] C →* ↥(A ⊔ C) :=
  (SemidirectProduct.monoidHomSubgroup hnorm).codRestrict (A ⊔ C)
    (fun x => Subgroup.mul_mem_sup x.left.property x.right.property)

@[simp] theorem toSup_coe (x : A ⋊[action A C hnorm] C) :
    ((toSup A C hnorm x : ↥(A ⊔ C)) : G) = (x.left : G) * (x.right : G) := rfl

/-- Disjointness gives uniqueness of the actual product coordinates. -/
theorem toSup_injective (hdisjoint : Disjoint A C) :
    Function.Injective (toSup A C hnorm) := by
  intro x y h
  apply SemidirectProduct.equivProd.injective
  exact Subgroup.mul_injective_of_disjoint hdisjoint
    (congrArg (fun z : ↥(A ⊔ C) => (z : G)) h)

/-- Normalization gives existence of the actual product coordinates. -/
theorem toSup_surjective : Function.Surjective (toSup A C hnorm) := by
  intro g
  have hg : (g : G) ∈ (A : Set G) * (C : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left A C hnorm]
    exact g.property
  obtain ⟨a, ha, c, hc, hac⟩ := hg
  refine ⟨⟨⟨a, ha⟩, ⟨c, hc⟩⟩, ?_⟩
  apply Subtype.ext
  exact hac

/-- The semidirect-product model is constructed from the actual subgroup hypotheses. -/
def supEquiv (hdisjoint : Disjoint A C) : A ⋊[action A C hnorm] C ≃* ↥(A ⊔ C) :=
  MulEquiv.ofBijective (toSup A C hnorm)
    ⟨toSup_injective A C hnorm hdisjoint, toSup_surjective A C hnorm⟩

@[simp] theorem supEquiv_mk (hdisjoint : Disjoint A C) (a : A) (c : C) :
    supEquiv A C hnorm hdisjoint ⟨a, c⟩ =
      ⟨(a : G) * (c : G), Subgroup.mul_mem_sup a.property c.property⟩ := rfl

variable {B : Type v} [Group B]
variable (χ : A →* B)
variable (hinvariant : ∀ (c : C) (a : A), χ (action A C hnorm c a) = χ a)

/-- The actual character on the semidirect model, trivial on the C factor. -/
def modelExtension : A ⋊[action A C hnorm] C →* B :=
  SemidirectProduct.lift χ (1 : C →* B) (fun c => by
    apply MonoidHom.ext
    intro a
    simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MonoidHom.one_apply, MulAut.conj_apply, one_mul, inv_one, mul_one] using hinvariant c a)

/-- The actual invariant character extends over the subgroup join. -/
def extension (hdisjoint : Disjoint A C) : ↥(A ⊔ C) →* B :=
  (modelExtension A C hnorm χ hinvariant).comp
    (supEquiv A C hnorm hdisjoint).symm.toMonoidHom

/-- The extension evaluates by the original character on the actual A coordinate. -/
theorem extension_apply_mul (hdisjoint : Disjoint A C) (a : A) (c : C) :
    extension A C hnorm χ hinvariant hdisjoint
      ⟨(a : G) * (c : G), Subgroup.mul_mem_sup a.property c.property⟩ = χ a := by
  change modelExtension A C hnorm χ hinvariant
    ((supEquiv A C hnorm hdisjoint).symm
      (supEquiv A C hnorm hdisjoint ⟨a, c⟩)) = χ a
  rw [MulEquiv.symm_apply_apply]
  change χ a * 1 = χ a
  exact mul_one _

@[simp] theorem extension_left (hdisjoint : Disjoint A C) (a : A) :
    extension A C hnorm χ hinvariant hdisjoint
      (Subgroup.inclusion (show A ≤ A ⊔ C from le_sup_left) a) = χ a := by
  change extension A C hnorm χ hinvariant hdisjoint ⟨(a : G), (show A ≤ A ⊔ C from le_sup_left) a.property⟩ = χ a
  simpa only [Subgroup.coe_one, mul_one] using
    extension_apply_mul A C hnorm χ hinvariant hdisjoint a 1

@[simp] theorem extension_right (hdisjoint : Disjoint A C) (c : C) :
    extension A C hnorm χ hinvariant hdisjoint
      (Subgroup.inclusion (show C ≤ A ⊔ C from le_sup_right) c) = 1 := by
  change extension A C hnorm χ hinvariant hdisjoint ⟨(c : G), (show C ≤ A ⊔ C from le_sup_right) c.property⟩ = 1
  simpa only [Subgroup.coe_one, one_mul, map_one] using
    extension_apply_mul A C hnorm χ hinvariant hdisjoint 1 c

/-- The extension agrees with the original homomorphism on the actual left subgroup. -/
theorem extension_comp_left (hdisjoint : Disjoint A C) :
    (extension A C hnorm χ hinvariant hdisjoint).comp
      (Subgroup.inclusion (show A ≤ A ⊔ C from le_sup_left)) = χ := by
  apply MonoidHom.ext
  exact extension_left A C hnorm χ hinvariant hdisjoint

/-- The extension is the trivial homomorphism on the actual supplement. -/
theorem extension_comp_right (hdisjoint : Disjoint A C) :
    (extension A C hnorm χ hinvariant hdisjoint).comp
      (Subgroup.inclusion (show C ≤ A ⊔ C from le_sup_right)) = 1 := by
  apply MonoidHom.ext
  exact extension_right A C hnorm χ hinvariant hdisjoint

include hnorm hinvariant in
/-- A directly usable actual extension, with both restriction equations. -/
theorem exists_extension (hdisjoint : Disjoint A C) :
    ∃ χhat : ↥(A ⊔ C) →* B,
      χhat.comp (Subgroup.inclusion (show A ≤ A ⊔ C from le_sup_left)) = χ ∧
      χhat.comp (Subgroup.inclusion (show C ≤ A ⊔ C from le_sup_right)) = 1 :=
  ⟨extension A C hnorm χ hinvariant hdisjoint,
    extension_comp_left A C hnorm χ hinvariant hdisjoint,
    extension_comp_right A C hnorm χ hinvariant hdisjoint⟩

end Kourovka2135.InvariantCharacterSupExtension
