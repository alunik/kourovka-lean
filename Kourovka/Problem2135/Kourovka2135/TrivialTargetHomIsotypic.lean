import Kourovka2135.RepresentationDualIrreducible
import Mathlib.RingTheory.SimpleModule.Isotypic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.Free

/-! The actual Hom representation with trivial target is a finite direct
sum of the contragredient. Its semisimplicity and isotypy are properties
of this individual module, with no semisimple group-algebra assumption. -/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.TrivialTargetHomIsotypic

open Representation Module
open scoped MonoidAlgebra

section Products

variable (R : Type*) [Ring R] (S : Type*) [AddCommGroup S] [Module R S]
variable [IsSimpleModule R S] (ι : Type*)

/-- Every simple submodule of a product of copies of one simple module
maps isomorphically onto one coordinate. Finiteness is unnecessary here. -/
theorem isIsotypicOfType_pi : IsIsotypicOfType R (ι → S) S := by
  intro T hT
  let : Nontrivial T := IsSimpleModule.nontrivial R T
  obtain ⟨t, ht⟩ := exists_ne (0 : T)
  have hex : ∃ i : ι, (t : ι → S) i ≠ 0 := by
    by_contra! h
    apply ht
    exact Subtype.ext (funext h)
  obtain ⟨i, hi⟩ := hex
  let f : T →ₗ[R] S := (LinearMap.proj i).comp T.subtype
  have hf : f ≠ 0 := by
    intro h
    exact hi (congrArg (fun a : T →ₗ[R] S => a t) h)
  exact ⟨LinearEquiv.ofBijective f (LinearMap.bijective_of_ne_zero hf)⟩

end Products

variable {k : Type*} [Field k] {G : Type*} [Group G]
variable {V : Type*} [AddCommGroup V] [Module k V]
variable (ρ : Representation k G V)
variable (Z : Type*) [AddCommGroup Z] [Module k Z]

/-- The actual group action on Hom(V,Z), with trivial action on Z. -/
abbrev homRepresentation : Representation k G (V →ₗ[k] Z) :=
  Representation.linHom ρ (Representation.trivial k G Z)

@[simp] theorem homRepresentation_apply (g : G) (f : V →ₗ[k] Z) (v : V) :
    homRepresentation ρ Z g f v = f (ρ g⁻¹ v) := rfl

/-- Postcomposition by a scalar coordinate is genuinely equivariant for
the contragredient action. -/
def coordinateIntertwiner (ell : Z →ₗ[k] k) :
    (homRepresentation ρ Z).IntertwiningMap ρ.dual where
  toLinearMap := {
    toFun := fun f => ell.comp f
    map_add' := fun f h => by
      ext v
      change ell (f v + h v) = ell (f v) + ell (h v)
      exact map_add ell _ _
    map_smul' := fun a f => by
      ext v
      change ell (a • f v) = a • ell (f v)
      exact map_smul ell _ _ }
  isIntertwining' g := by
    ext f v
    rfl

variable {ι : Type*} (b : Basis ι k Z)

/-- Actual basis coordinates assembled as a group-algebra linear map. -/
def coordinates : (homRepresentation ρ Z).asModule →ₗ[k[G]] (ι → ρ.dual.asModule) :=
  LinearMap.pi (fun i =>
    IntertwiningMap.equivLinearMapAsModule (homRepresentation ρ Z) ρ.dual
      (coordinateIntertwiner ρ Z (b.coord i)))

@[simp] theorem coordinates_apply (f : (homRepresentation ρ Z).asModule)
    (i : ι) (v : V) :
    ρ.dual.asModuleEquiv (coordinates ρ Z b f i) v =
      b.coord i ((homRepresentation ρ Z).asModuleEquiv f v) := rfl

variable [Finite ι]

theorem coordinates_injective : Function.Injective (coordinates ρ Z b) := by
  intro f h hfh
  apply (homRepresentation ρ Z).asModuleEquiv.injective
  apply LinearMap.ext
  intro v
  apply b.equivFun.injective
  funext i
  have h := congrArg (fun a : ι → ρ.dual.asModule => ρ.dual.asModuleEquiv (a i) v) hfh
  simpa only [coordinates_apply, Basis.coord_apply, Basis.equivFun_apply] using h

theorem coordinates_surjective : Function.Surjective (coordinates ρ Z b) := by
  intro a
  let f : V →ₗ[k] Z := b.equivFun.symm.toLinearMap.comp
    (LinearMap.pi (fun i => ρ.dual.asModuleEquiv (a i)))
  refine ⟨(homRepresentation ρ Z).asModuleEquiv.symm f, ?_⟩
  funext i
  apply ρ.dual.asModuleEquiv.injective
  apply LinearMap.ext
  intro v
  change b.coord i (b.equivFun.symm (fun j => ρ.dual.asModuleEquiv (a j) v)) =
    ρ.dual.asModuleEquiv (a i) v
  exact b.coord_equivFun_symm i _

/-- A basis of the trivial target identifies the actual group-algebra
Hom module with the corresponding copies of the actual dual module. -/
def coordinatesEquiv : (homRepresentation ρ Z).asModule ≃ₗ[k[G]] (ι → ρ.dual.asModule) :=
  LinearEquiv.ofBijective (coordinates ρ Z b)
    ⟨coordinates_injective ρ Z b, coordinates_surjective ρ Z b⟩

section FiniteDimension

variable [FiniteDimensional k V] [FiniteDimensional k Z]

/-- The particular Hom module is finitely generated over the group algebra. -/
theorem moduleFinite : Module.Finite k[G] (homRepresentation ρ Z).asModule :=
  Module.Finite.of_restrictScalars_finite k k[G] (homRepresentation ρ Z).asModule

variable [ρ.IsIrreducible]

/-- The actual finite Hom representation is semisimple by its explicit
coordinate equivalence with a finite product of simple dual modules. -/
theorem isSemisimpleModule : IsSemisimpleModule k[G] (homRepresentation ρ Z).asModule := by
  let : ρ.dual.IsIrreducible := RepresentationDualIrreducible.isIrreducible_dual ρ
  exact IsSemisimpleModule.congr
    (M := Fin (Module.finrank k Z) → ρ.dual.asModule)
    (coordinatesEquiv ρ Z (Module.finBasis k Z))

/-- Every simple constituent of the actual Hom module is the actual dual. -/
theorem isIsotypicOfType :
    IsIsotypicOfType k[G] (homRepresentation ρ Z).asModule ρ.dual.asModule := by
  let : ρ.dual.IsIrreducible := RepresentationDualIrreducible.isIrreducible_dual ρ
  let e := coordinatesEquiv ρ Z (Module.finBasis k Z)
  exact (isIsotypicOfType_pi k[G] ρ.dual.asModule (Fin (Module.finrank k Z))).of_injective
    e.toLinearMap e.injective

variable {W : Type*} [AddCommGroup W] [Module k W]
variable (τ : Representation k G W)
variable (f : τ.IntertwiningMap (homRepresentation ρ Z)) (hf : Function.Injective f)

include f hf

/-- An actual embedded representation inherits semisimplicity from the
particular Hom module, without a group-algebra semisimplicity assumption. -/
theorem isSemisimpleModule_of_injective : IsSemisimpleModule k[G] τ.asModule := by
  let : IsSemisimpleModule k[G] (homRepresentation ρ Z).asModule := isSemisimpleModule ρ Z
  exact IsSemisimpleModule.of_injective
    (IntertwiningMap.equivLinearMapAsModule τ (homRepresentation ρ Z) f) hf

/-- An actual embedded representation has only dual-type simple constituents. -/
theorem isIsotypicOfType_of_injective : IsIsotypicOfType k[G] τ.asModule ρ.dual.asModule :=
  (isIsotypicOfType ρ Z).of_injective
    (IntertwiningMap.equivLinearMapAsModule τ (homRepresentation ρ Z) f) hf

omit [ρ.IsIrreducible] in
/-- The injective coordinate map also proves finite-dimensionality of its source. -/
theorem finiteDimensional_of_injective : FiniteDimensional k W :=
  FiniteDimensional.of_injective f.toLinearMap hf

end FiniteDimension

end Kourovka2135.TrivialTargetHomIsotypic
