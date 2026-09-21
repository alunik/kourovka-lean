/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors

The base-change construction, endomorphism-equivalence calculation, and
full-endomorphism-action irreducibility criterion adapt the Apache-2.0 sources
TauCeti/RepresentationTheory/BaseChange.lean and
TauCeti/RepresentationTheory/Irreducible.lean at commit
7a4e28011b29a4e8c8365fe87f2144022cf1377f.
The density-preservation argument and actual EndField endpoint are new adapters.
-/
import Kourovka2135.RepresentationEndDensity
import Mathlib.RingTheory.TensorProduct.IsBaseChangeHom
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! Scalar extension of an individual representation whose algebra action is
surjective onto its full endomorphism ring. The actual tensor-product action
remains surjective, hence irreducible. Applied to the audited density theorem
for `overEnd`, this proves irreducibility after every field extension of the
actual commuting field. No semisimplicity of the whole group algebra and no
absolute-irreducibility premise is used.

-/
set_option autoImplicit false
noncomputable section

namespace Kourovka2135.RepresentationDensityBaseChange
open TensorProduct
open scoped MonoidAlgebra

section BaseChange
variable {E L G V : Type*} [Field E] [Field L] [Algebra E L]
variable [Monoid G] [AddCommGroup V] [Module E V]

/-- The actual scalar-extended representation, obtained by extending each operator. -/
def baseChange (L : Type*) [Field L] [Algebra E L]
    (ρ : Representation E G V) : Representation L G (L ⊗[E] V) :=
  ((Module.End.baseChangeHom E L V :
    Module.End E V →ₐ[E] Module.End L (L ⊗[E] V)) :
      Module.End E V →* Module.End L (L ⊗[E] V)).comp ρ

@[simp] theorem baseChange_apply (ρ : Representation E G V) (g : G) :
    baseChange L ρ g = (ρ g).baseChange L := rfl

/-- Extending a group-algebra coefficient and extending its operator agree. -/
theorem baseChange_asAlgebraHom_mapRingHom (ρ : Representation E G V) (r : E[G]) :
    (baseChange L ρ).asAlgebraHom
      (MonoidAlgebra.mapRingHom G (algebraMap E L) r) =
        (ρ.asAlgebraHom r).baseChange L := by
  induction r using MonoidAlgebra.induction_linear with
  | zero => simp
  | add r s hr hs => simp only [map_add, LinearMap.baseChange_add, hr, hs]
  | single g a =>
      rw [MonoidAlgebra.mapRingHom_single, Representation.asAlgebraHom_single,
        Representation.asAlgebraHom_single, baseChange_apply, LinearMap.baseChange_smul]
      exact IsScalarTower.algebraMap_smul L a ((ρ g).baseChange L)

variable [FiniteDimensional E V]

/-- Every endomorphism after scalar extension is a sum of scalar-extended operators. -/
def endBaseChangeEquiv :
    L ⊗[E] Module.End E V ≃ₗ[L] Module.End L (L ⊗[E] V) :=
  ((TensorProduct.isBaseChange E V L).linearMapLeftRight
    (TensorProduct.isBaseChange E V L)).equiv

/-- The endomorphism equivalence is the expected map on actual pure tensors. -/
theorem endBaseChangeEquiv_tmul (a : L) (T : Module.End E V) :
    endBaseChangeEquiv (E := E) (L := L) (V := V) (a ⊗ₜ[E] T) =
      a • T.baseChange L := by
  rw [endBaseChangeEquiv, IsBaseChange.equiv_tmul]
  congr 1
  ext v
  exact IsBaseChange.linearMapLeftRightHom_comp_apply (TensorProduct.isBaseChange E V L)
    ((TensorProduct.mk E L V) 1) T v

/-- Full endomorphism action for an individual module persists under field extension. -/
theorem baseChange_asAlgebraHom_surjective (ρ : Representation E G V)
    (hρ : Function.Surjective ρ.asAlgebraHom) :
    Function.Surjective (baseChange L ρ).asAlgebraHom := by
  intro T
  obtain ⟨z, rfl⟩ := (endBaseChangeEquiv (E := E) (L := L) (V := V)).surjective T
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | add z w hz hw =>
      obtain ⟨r, hr⟩ := hz
      obtain ⟨s, hs⟩ := hw
      exact ⟨r + s, by simp only [map_add, hr, hs]⟩
  | tmul a T =>
      obtain ⟨r, rfl⟩ := hρ T
      refine ⟨a • MonoidAlgebra.mapRingHom G (algebraMap E L) r, ?_⟩
      rw [map_smul, baseChange_asAlgebraHom_mapRingHom, endBaseChangeEquiv_tmul]

end BaseChange

section Irreducibility
variable {E G V : Type*} [Field E] [Monoid G] [AddCommGroup V] [Module E V]

/-- A nonzero vector space with full endomorphism action has no proper invariant subspace. -/
theorem isIrreducible_of_asAlgebraHom_surjective [Nontrivial V]
    (ρ : Representation E G V) (hρ : Function.Surjective ρ.asAlgebraHom) :
    ρ.IsIrreducible := by
  rw [Representation.irreducible_iff_isSimpleModule_asModule,
    isSimpleModule_iff_toSpanSingleton_surjective]
  refine ⟨ρ.asModuleEquiv.toEquiv.nontrivial, fun x hx y => ?_⟩
  obtain ⟨T, hT⟩ := IsSimpleModule.toSpanSingleton_surjective (Module.End E V)
    (m := ρ.asModuleEquiv x) (by simpa using hx) (ρ.asModuleEquiv y)
  rw [LinearMap.toSpanSingleton_apply, Module.End.smul_def] at hT
  obtain ⟨r, rfl⟩ := hρ T
  refine ⟨r, ρ.asModuleEquiv.injective ?_⟩
  rw [LinearMap.toSpanSingleton_apply, Representation.asModuleEquiv_map_smul, hT]

/-- Density proves absolute irreducibility by constructing each extended action. -/
theorem baseChange_isIrreducible (L : Type*) [Field L] [Algebra E L]
    [FiniteDimensional E V] [Nontrivial V] (ρ : Representation E G V)
    (hρ : Function.Surjective ρ.asAlgebraHom) : (baseChange L ρ).IsIrreducible := by
  let : Nontrivial (L ⊗[E] V) := Module.nontrivial_of_finrank_pos (R := L) (by
    rw [Module.finrank_baseChange]
    exact Module.finrank_pos)
  exact isIrreducible_of_asAlgebraHom_surjective (baseChange L ρ)
    (baseChange_asAlgebraHom_surjective ρ hρ)

end Irreducibility

section ActualEndField
open MinimalEndMovingRank
variable {K G V : Type*} [Field K] [Group G] [AddCommGroup V] [Module K V]
variable [Finite V] (ρ : Representation K G V) [ρ.IsIrreducible]

/-- The actual commuting-field representation stays dense after every field extension. -/
theorem overEnd_baseChange_asAlgebraHom_surjective (L : Type*) [Field L]
    [Algebra (EndField ρ) L] :
    Function.Surjective (baseChange L (overEnd ρ)).asAlgebraHom :=
  baseChange_asAlgebraHom_surjective (overEnd ρ)
    (RepresentationEndDensity.overEnd_asAlgebraHom_surjective ρ)

/-- The actual commuting-field representation is absolutely irreducible;
this endpoint derives its hypothesis from the already-proved original simplicity. -/
theorem overEnd_baseChange_isIrreducible (L : Type*) [Field L]
    [Algebra (EndField ρ) L] : (baseChange L (overEnd ρ)).IsIrreducible := by
  let : Nontrivial ρ.asModule := IsSimpleModule.nontrivial K[G] ρ.asModule
  let : Nontrivial V := ρ.asModuleEquiv.symm.toEquiv.nontrivial
  exact baseChange_isIrreducible L (overEnd ρ)
    (RepresentationEndDensity.overEnd_asAlgebraHom_surjective ρ)

end ActualEndField
end Kourovka2135.RepresentationDensityBaseChange
