import Mathlib.RepresentationTheory.Irreducible
import Mathlib.RingTheory.Artinian.Module
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Actual irreducible subrepresentations from finite dimensionality.

The actual group-algebra module is Artinian by restriction of its submodule
order to scalar subspaces. An atom gives an irreducible subrepresentation
on its own underlying subspace, with its actual inclusion intertwiner.
No semisimplicity, finite group, or characteristic assumption is used.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.RepresentationIrreducibleSubspace

open scoped MonoidAlgebra

variable {k G V : Type*} [Field k] [Monoid G] [AddCommGroup V] [Module k V]
variable {ρ : Representation k G V}

/-- The actual inclusion of an invariant subspace is an intertwiner. -/
def subtypeIntertwiner (W : Subrepresentation ρ) : W.toRepresentation.IntertwiningMap ρ where
  toLinearMap := W.toSubmodule.subtype
  isIntertwining' _ := by ext v; rfl

@[simp] theorem subtypeIntertwiner_apply (W : Subrepresentation ρ) (v : W.toSubmodule) :
    subtypeIntertwiner W v = (v : V) := rfl

theorem subtypeIntertwiner_injective (W : Subrepresentation ρ) :
    Function.Injective (subtypeIntertwiner W) := Subtype.coe_injective

/-- The restricted representation's actual group-algebra module is the original
invariant subspace with its inherited group-algebra action. -/
def moduleEquiv (W : Subrepresentation ρ) :
    W.toRepresentation.asModule ≃ₗ[k[G]] W.asSubmodule := by
  let f : W.toRepresentation.asModule →ₗ[k[G]] ρ.asModule :=
    Representation.IntertwiningMap.equivLinearMapAsModule W.toRepresentation ρ
      (subtypeIntertwiner W)
  let j : W.toRepresentation.asModule →ₗ[k[G]] W.asSubmodule :=
    f.codRestrict W.asSubmodule (fun v => v.property)
  exact LinearEquiv.ofBijective j
    ⟨fun x y h => Subtype.ext
      (congrArg (fun z : W.asSubmodule => (z : ρ.asModule)) h),
      fun y => ⟨⟨(y : ρ.asModule), y.property⟩, rfl⟩⟩

/-- An atom in the actual invariant-subspace lattice is irreducible on that subspace. -/
theorem isIrreducible_toRepresentation_of_isAtom (W : Subrepresentation ρ)
    (hW : IsAtom W) : W.toRepresentation.IsIrreducible := by
  have hA : IsAtom W.asSubmodule :=
    (Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ)).isAtom_iff W |>.mpr hW
  let : IsSimpleModule k[G] W.asSubmodule := isSimpleModule_iff_isAtom.mpr hA
  let : IsSimpleModule k[G] W.toRepresentation.asModule :=
    IsSimpleModule.congr (moduleEquiv W)
  exact (Representation.irreducible_iff_isSimpleModule_asModule W.toRepresentation).mpr
    inferInstance

/-- A scalar action restricts to the same scalar on the actual invariant subspace. -/
theorem toRepresentation_eq_smul_one (W : Subrepresentation ρ) (g : G) (c : k)
    (hscalar : ρ g = c • (1 : Module.End k V)) :
    W.toRepresentation g = c • (1 : Module.End k W.toSubmodule) := by
  ext v
  change ρ g (v : V) = c • (v : V)
  rw [hscalar]
  rfl

/-- A scalar different from one acts nontrivially on every nonzero invariant subspace. -/
theorem toRepresentation_ne_one_of_scalar (W : Subrepresentation ρ)
    [Nontrivial W.toSubmodule] (g : G) (c : k)
    (hscalar : ρ g = c • (1 : Module.End k V)) (hc : c ≠ 1) :
    W.toRepresentation g ≠ 1 := by
  intro h
  obtain ⟨v, hv⟩ := exists_ne (0 : W.toSubmodule)
  have hcv : c • v = v := by
    have h' := congrArg (fun a : Module.End k W.toSubmodule => a v) h
    simpa only [toRepresentation_eq_smul_one W g c hscalar,
      LinearMap.smul_apply, Module.End.one_apply] using h'
  have hz : (c - 1) • v = 0 := by
    rw [sub_smul, one_smul, hcv, sub_self]
  exact hv ((smul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hc))

variable (ρ) [FiniteDimensional k V] [Nontrivial V]

/-- The actual invariant-subspace lattice contains an atom by scalar Artinianness. -/
theorem exists_isAtom_subrepresentation : ∃ W : Subrepresentation ρ, IsAtom W := by
  let : Nontrivial ρ.asModule := ρ.asModuleEquiv.toEquiv.nontrivial
  let : IsArtinian k[G] ρ.asModule :=
    isArtinian_of_tower k (inferInstance : IsArtinian k ρ.asModule)
  obtain ⟨A, hA⟩ := IsAtomic.exists_atom (Submodule k[G] ρ.asModule)
  let e := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ)
  exact ⟨e.symm A, (e.symm.isAtom_iff A).mpr hA⟩

/-- Every finite-dimensional nonzero actual representation contains an actual
nonzero irreducible subrepresentation, without Maschke's theorem. -/
theorem exists_irreducible_subrepresentation :
    ∃ W : Subrepresentation ρ, W ≠ ⊥ ∧ W.toRepresentation.IsIrreducible := by
  obtain ⟨W, hW⟩ := exists_isAtom_subrepresentation ρ
  exact ⟨W, hW.ne_bot, isIrreducible_toRepresentation_of_isAtom W hW⟩

/-- If every actual irreducible subrepresentation has the full ambient dimension,
the whole representation is irreducible. -/
theorem isIrreducible_of_irreducible_finrank_eq
    (hdegree : ∀ W : Subrepresentation ρ, W.toRepresentation.IsIrreducible →
      Module.finrank k W.toSubmodule = Module.finrank k V) : ρ.IsIrreducible := by
  obtain ⟨W, hW⟩ := exists_isAtom_subrepresentation ρ
  have hdim := hdegree W (isIrreducible_toRepresentation_of_isAtom W hW)
  have htop : W = ⊤ := Subrepresentation.toSubmodule_injective
    (Submodule.eq_top_iff_finrank_eq.mpr hdim)
  exact isSimpleOrder_iff_isAtom_top.mpr (htop ▸ hW)

end Kourovka2135.RepresentationIrreducibleSubspace
