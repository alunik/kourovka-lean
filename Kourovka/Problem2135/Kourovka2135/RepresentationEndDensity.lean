/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors

The evaluation-transport proof is adapted from
TauCeti/RepresentationTheory/Irreducible.lean,
commit 7a4e28011b29a4e8c8365fe87f2144022cf1377f.
The algebraically closed Schur step is replaced by the actual commuting field.
-/
import Kourovka2135.MinimalEndMovingRank
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.Algebra.MonoidAlgebra.MapDomain

/-! Density for the actual commuting endomorphism field of a finite
irreducible representation. The original group algebra exhausts the
endomorphisms linear over that field; extending its coefficients therefore
makes the actual `overEnd` algebra action surjective. No global semisimple
group-algebra or algebraic-closure hypothesis is used.

The evaluation transport adapts the density proof in TauCeti's
`RepresentationTheory/Irreducible.lean` (Apache-2.0), replacing its
algebraically closed Schur step by our actual commuting-field action.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.RepresentationEndDensity

open MinimalEndMovingRank
open scoped MonoidAlgebra

variable {K G V : Type*} [Field K] [Group G] [AddCommGroup V] [Module K V]
variable [Finite V] (ρ : Representation K G V) [ρ.IsIrreducible]

omit [Finite V] [ρ.IsIrreducible] in
/-- The intertwiner/group-algebra-endomorphism equivalence preserves evaluation. -/
theorem equivAlgEnd_apply (e : EndField ρ) (v : ρ.asModule) :
    Representation.IntertwiningMap.equivAlgEnd (ρ := ρ) e v = e v := rfl

/-- Jacobson density transported to the original representation and its actual
commuting field: every E-linear operator is a genuine K-group-algebra action. -/
theorem exists_groupAlgebra_action_eq_overEnd (T : Module.End (EndField ρ) V) :
    ∃ r : K[G], ∀ v : V, ρ.asAlgebraHom r v = T v := by
  classical
  have : Finite ρ.asModule :=
    Finite.of_injective ρ.asModuleEquiv ρ.asModuleEquiv.injective
  let e := Representation.IntertwiningMap.equivAlgEnd (ρ := ρ)
  let T' : Module.End (Module.End K[G] ρ.asModule) ρ.asModule :=
    { toFun := T
      map_add' := T.map_add
      map_smul' := fun F v => by
        obtain ⟨F', rfl⟩ := e.surjective F
        change T (F' v) = F' (T v)
        exact T.map_smul F' v }
  obtain ⟨r, hr⟩ :=
    Module.Finite.toModuleEnd_moduleEnd_surjective (R := K[G]) (M := ρ.asModule) T'
  refine ⟨r, fun v => ?_⟩
  have hT' (x : ρ.asModule) : T' x = T x := rfl
  have hv := LinearMap.congr_fun hr (ρ.asModuleEquiv.symm v)
  rw [hT'] at hv
  have hv' := congrArg ρ.asModuleEquiv hv
  have hT_equiv : ρ.asModuleEquiv (T (ρ.asModuleEquiv.symm v)) = T v := rfl
  rw [hT_equiv] at hv'
  simpa only [Module.toModuleEnd_apply, DistribSMul.toLinearMap_apply,
    Representation.asModuleEquiv_map_smul, LinearEquiv.apply_symm_apply] using hv'

/-- Extending group-algebra coefficients changes no underlying action. -/
theorem overEnd_asAlgebraHom_mapRingHom_apply (r : K[G]) (v : V) :
    (overEnd ρ).asAlgebraHom
        (MonoidAlgebra.mapRingHom G (algebraMap K (EndField ρ)) r) v =
      ρ.asAlgebraHom r v := by
  induction r using MonoidAlgebra.induction_linear with
  | zero => simp
  | add r s hr hs => simp only [map_add, LinearMap.add_apply, hr, hs]
  | single g a =>
    rw [MonoidAlgebra.mapRingHom_single, Representation.asAlgebraHom_single,
      Representation.asAlgebraHom_single]
    change (algebraMap K (EndField ρ) a) • (ρ g v) = a • (ρ g v)
    exact IsScalarTower.algebraMap_smul _ _ _

/-- The actual representation over its commuting field exhausts all linear
endomorphisms, with no semisimplicity assumption on the whole group algebra. -/
theorem overEnd_asAlgebraHom_surjective :
    Function.Surjective (overEnd ρ).asAlgebraHom := by
  intro T
  obtain ⟨r, hr⟩ := exists_groupAlgebra_action_eq_overEnd ρ T
  refine ⟨MonoidAlgebra.mapRingHom G (algebraMap K (EndField ρ)) r, ?_⟩
  apply LinearMap.ext
  intro v
  rw [overEnd_asAlgebraHom_mapRingHom_apply]
  exact hr v

end Kourovka2135.RepresentationEndDensity
