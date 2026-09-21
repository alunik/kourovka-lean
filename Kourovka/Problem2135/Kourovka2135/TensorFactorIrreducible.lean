import Mathlib.RepresentationTheory.Irreducible
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-! An irreducible tensor product has irreducible nonzero factors.

Tensoring the actual inclusion of a subrepresentation gives an intertwiner
into the simple tensor product. Faithful flatness of a nonzero vector space
reflects both its nonvanishing and its surjectivity. No finite-dimensionality,
semisimplicity, classification, or tensor decomposition assumption is needed.
-/

set_option autoImplicit false
noncomputable section
open scoped MonoidAlgebra
namespace Kourovka2135.TensorFactorIrreducible

variable {k G V W : Type*} [Field k] [Monoid G]
variable [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
variable (ρ : Representation k G V) (σ : Representation k G W)

/-- Transport simplicity through an actual intertwining equivalence. -/
theorem of_equiv [σ.IsIrreducible] (a : ρ.Equiv σ) : ρ.IsIrreducible := by
  let f : ρ.asModule →ₗ[k[G]] σ.asModule :=
    Representation.IntertwiningMap.equivLinearMapAsModule ρ σ a.toIntertwiningMap
  let e : ρ.asModule ≃ₗ[k[G]] σ.asModule :=
    LinearEquiv.ofBijective f a.toLinearEquiv.bijective
  let : IsSimpleModule k[G] ρ.asModule := IsSimpleModule.congr (N := σ.asModule) e
  exact (Representation.irreducible_iff_isSimpleModule_asModule ρ).mpr inferInstance

/-- The actual subtype inclusion of a subrepresentation. -/
def subtypeHom (S : Subrepresentation ρ) : S.toRepresentation.IntertwiningMap ρ :=
  ⟨S.toSubmodule.subtype, by intro g; rfl⟩

theorem subtypeHom_ne_zero (S : Subrepresentation ρ) (hS : S ≠ ⊥) : subtypeHom ρ S ≠ 0 := by
  intro h
  apply hS
  apply Subrepresentation.toSubmodule_injective
  apply (Submodule.eq_bot_iff _).mpr
  intro v hv
  exact congrArg (fun f : S.toRepresentation.IntertwiningMap ρ => f ⟨v, hv⟩) h

/-- Simplicity follows when every nonzero subrepresentation inclusion is onto. -/
theorem isIrreducible_of_subtype_surjective [Nontrivial V]
    (h : ∀ S : Subrepresentation ρ, S ≠ ⊥ → Function.Surjective (subtypeHom ρ S)) :
    ρ.IsIrreducible := by
  obtain ⟨v, hv⟩ : ∃ v : V, v ≠ 0 := exists_ne 0
  have hbot : (⊥ : Subrepresentation ρ) ≠ ⊤ := by
    intro he
    apply hv
    have hm : v ∈ (⊥ : Subrepresentation ρ).toSubmodule := by rw [he]; trivial
    exact hm
  let : Nontrivial (Subrepresentation ρ) := ⟨⟨⊥, ⊤, hbot⟩⟩
  apply IsSimpleOrder.of_forall_eq_top
  intro S hS
  apply Subrepresentation.toSubmodule_injective
  apply top_unique
  intro x _
  obtain ⟨y, hy⟩ := h S hS x
  exact hy ▸ y.property

/-- Any nonzero left factor of a simple tensor product is simple. -/
theorem left [Nontrivial V] [Nontrivial W] [(ρ.tprod σ).IsIrreducible] :
    ρ.IsIrreducible := by
  apply isIrreducible_of_subtype_surjective ρ
  intro S hS
  let i := subtypeHom ρ S
  have hi : i ≠ 0 := subtypeHom_ne_zero ρ S hS
  have ht : i.rTensor σ ≠ 0 := by
    intro h
    apply hi
    apply Representation.IntertwiningMap.ext
    apply (Module.FaithfullyFlat.zero_iff_rTensor_zero k W i.toLinearMap).mpr
    exact congrArg Representation.IntertwiningMap.toLinearMap h
  have hs := (Representation.IsIrreducible.surjective_or_eq_zero (i.rTensor σ)).resolve_right ht
  have hr : Function.Surjective (i.toLinearMap.rTensor W) := hs
  have hl : Function.Surjective (i.toLinearMap.lTensor W) :=
    (i.toLinearMap.lTensor_surj_iff_rTensor_surj W).mpr hr
  exact (Module.FaithfullyFlat.lTensor_surjective_iff_surjective k W i.toLinearMap).mp hl

/-- Any nonzero right factor of a simple tensor product is simple. -/
theorem right [Nontrivial V] [Nontrivial W] [(ρ.tprod σ).IsIrreducible] :
    σ.IsIrreducible := by
  apply isIrreducible_of_subtype_surjective σ
  intro S hS
  let i := subtypeHom σ S
  have hi : i ≠ 0 := subtypeHom_ne_zero σ S hS
  have ht : i.lTensor ρ ≠ 0 := by
    intro h
    apply hi
    apply Representation.IntertwiningMap.ext
    apply (Module.FaithfullyFlat.zero_iff_lTensor_zero k V i.toLinearMap).mpr
    exact congrArg Representation.IntertwiningMap.toLinearMap h
  have hs := (Representation.IsIrreducible.surjective_or_eq_zero (i.lTensor ρ)).resolve_right ht
  have hl : Function.Surjective (i.toLinearMap.lTensor V) := hs
  exact (Module.FaithfullyFlat.lTensor_surjective_iff_surjective k V i.toLinearMap).mp hl

/-- Both conclusions with the actual tensor-product hypothesis explicit. -/
theorem factors [Nontrivial V] [Nontrivial W] (h : (ρ.tprod σ).IsIrreducible) :
    ρ.IsIrreducible ∧ σ.IsIrreducible := by
  let : (ρ.tprod σ).IsIrreducible := h
  exact ⟨left ρ σ, right ρ σ⟩

end Kourovka2135.TensorFactorIrreducible
