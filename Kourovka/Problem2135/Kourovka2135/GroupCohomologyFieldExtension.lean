/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors

The kernel-dimension transport pattern adapts
TauCeti/RepresentationTheory/BaseChange.lean, commit
7a4e28011b29a4e8c8365fe87f2144022cf1377f (Apache-2.0).
The ordinary group-cochain comparison and homology adapters below are new.
-/
import Kourovka2135.RepresentationDensityBaseChange
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Ordinary positive-degree group
cohomology has unchanged dimension under a field extension. The proof uses the
actual finite-function cochain differentials, flat kernel transport, and the
dimension formula for a short complex. No cohomology comparison is assumed.
-/

set_option autoImplicit false
noncomputable section
universe u

namespace Kourovka2135.GroupCohomologyFieldExtension

open CategoryTheory TensorProduct
open RepresentationDensityBaseChange

section ShortComplex

variable {E : Type u} [Field E] (S : ShortComplex (ModuleCat.{u} E))

/-- A dimension identity that avoids truncated subtraction and range transports. -/
theorem finrank_homology_add_finrank_source
    [FiniteDimensional E S.X₁] [FiniteDimensional E S.X₂] :
    Module.finrank E S.homology + Module.finrank E S.X₁ =
      Module.finrank E (LinearMap.ker S.g.hom) +
        Module.finrank E (LinearMap.ker S.f.hom) := by
  have hquot := (LinearMap.range S.moduleCatToCycles).finrank_quotient_add_finrank
  have hrank := S.moduleCatToCycles.finrank_range_add_finrank_ker
  have hhom := S.moduleCatHomologyIso.toLinearEquiv.finrank_eq
  change Module.finrank E S.homology =
    Module.finrank E (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles) at hhom
  have hker : LinearMap.ker S.moduleCatToCycles = LinearMap.ker S.f.hom := by
    ext x
    change (S.moduleCatToCycles x = 0) ↔ S.f.hom x = 0
    constructor
    · intro h
      exact congrArg Subtype.val h
    · intro h
      exact Subtype.ext h
  rw [hker] at hrank
  omega

/-- A finite-dimensional middle term gives finite-dimensional actual homology. -/
theorem finiteDimensional_shortComplex_homology [FiniteDimensional E S.X₂] :
    FiniteDimensional E S.homology := by
  let : FiniteDimensional E S.moduleCatLeftHomologyData.H := by
    change FiniteDimensional E
      (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles)
    infer_instance
  exact FiniteDimensional.of_injective S.moduleCatHomologyIso.hom.hom
    S.moduleCatHomologyIso.toLinearEquiv.injective

end ShortComplex

section Cochains

variable {E L G V : Type u} [Field E] [Field L] [Algebra E L]
variable [Group G] [Finite G] [AddCommGroup V] [Module E V]

/-- The finite-function tensor equivalence in cochain degree `n`. -/
def cochainsEquiv (n : ℕ) :
    L ⊗[E] ((Fin n → G) → V) ≃ₗ[L] ((Fin n → G) → L ⊗[E] V) := by
  classical
  let : Fintype G := Fintype.ofFinite G
  exact TensorProduct.piRight E L L (fun _ : Fin n → G => V)

omit [Group G] in
@[simp] theorem cochainsEquiv_tmul (n : ℕ) (a : L) (v : (Fin n → G) → V) :
    cochainsEquiv (E := E) (G := G) n (a ⊗ₜ[E] v) = fun g => a ⊗ₜ[E] v g := rfl

/-- The actual ordinary cochain differential, as an unbundled linear map. -/
abbrev differential (ρ : Representation E G V) (n : ℕ) :
    ((Fin n → G) → V) →ₗ[E] ((Fin (n + 1) → G) → V) :=
  (inhomogeneousCochains.d (Rep.of ρ) n).hom

private theorem tmul_smul_algebraMap (a : L) (r : E) (v : V) :
    a ⊗ₜ[E] (r • v) = algebraMap E L r • (a ⊗ₜ[E] v) := by
  calc
    _ = r • (a ⊗ₜ[E] v) := TensorProduct.tmul_smul r a v
    _ = _ := (IsScalarTower.algebraMap_smul L r (a ⊗ₜ[E] v)).symm

omit [Finite G] in
/-- Tensoring an actual cochain commutes with its group-cohomology differential. -/
theorem differential_tmul (ρ : Representation E G V) (n : ℕ)
    (a : L) (v : (Fin n → G) → V) :
    differential (baseChange L ρ) n (fun g => a ⊗ₜ[E] v g) =
      fun g => a ⊗ₜ[E] differential ρ n v g := by
  ext g
  simp only [differential, inhomogeneousCochains.d_hom_apply,
    baseChange_apply, LinearMap.baseChange_tmul, TensorProduct.tmul_add,
    TensorProduct.tmul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [tmul_smul_algebraMap]
  simp

/-- The degreewise tensor equivalences intertwine the actual differentials. -/
theorem cochainsEquiv_differential (ρ : Representation E G V) (n : ℕ)
    (z : L ⊗[E] ((Fin n → G) → V)) :
    cochainsEquiv (E := E) (G := G) (n + 1) ((differential ρ n).baseChange L z) =
      differential (baseChange L ρ) n (cochainsEquiv (E := E) (G := G) n z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z w hz hw => simp only [map_add, hz, hw]
  | tmul a v =>
      simp only [LinearMap.baseChange_tmul, cochainsEquiv_tmul, differential_tmul]

/-- The actual extended differential kernel pulls back to the tensor kernel. -/
theorem comap_ker_differential (ρ : Representation E G V) (n : ℕ) :
    Submodule.comap (cochainsEquiv (E := E) (L := L) (G := G) (V := V) n).toLinearMap
      (LinearMap.ker (differential (baseChange L ρ) n)) =
        LinearMap.ker ((differential ρ n).baseChange L) := by
  ext z
  simp only [Submodule.mem_comap, LinearMap.mem_ker, LinearEquiv.coe_coe]
  rw [← cochainsEquiv_differential]
  exact (cochainsEquiv (E := E) (L := L) (G := G) (V := V) (n + 1)).map_eq_zero_iff

/-- Flatness preserves the dimension of an arbitrary linear-map kernel. -/
theorem finrank_ker_baseChange {M N : Type u} [AddCommGroup M] [Module E M]
    [AddCommGroup N] [Module E N] (f : M →ₗ[E] N) :
    Module.finrank L (LinearMap.ker (f.baseChange L)) =
      Module.finrank E (LinearMap.ker f) :=
  ((LinearMap.tensorKerEquiv L L f).finrank_eq).symm.trans Module.finrank_baseChange

/-- Ordinary differential kernels have the same dimensions after field extension. -/
theorem finrank_ker_differential (ρ : Representation E G V) (n : ℕ) :
    Module.finrank L (LinearMap.ker (differential (baseChange L ρ) n)) =
      Module.finrank E (LinearMap.ker (differential ρ n)) := by
  rw [← (LinearEquiv.ofSubmodule'
    (cochainsEquiv (E := E) (L := L) (G := G) (V := V) n)
    (LinearMap.ker (differential (baseChange L ρ) n))).finrank_eq,
    comap_ker_differential]
  exact finrank_ker_baseChange _

omit [Group G] in
/-- The finite cochain spaces have unchanged dimensions. -/
theorem finrank_cochains (n : ℕ) :
    Module.finrank L ((Fin n → G) → L ⊗[E] V) =
      Module.finrank E ((Fin n → G) → V) :=
  (cochainsEquiv (E := E) (L := L) (G := G) (V := V) n).finrank_eq.symm.trans
    Module.finrank_baseChange

variable [FiniteDimensional E V]

/-- Finite groups and finite coefficient spaces give finite-dimensional ordinary cohomology. -/
theorem finiteDimensional_groupCohomology (ρ : Representation E G V) (n : ℕ) :
    FiniteDimensional E (groupCohomology (Rep.of ρ) (n + 1)) := by
  let C := groupCohomology.inhomogeneousCochains (Rep.of ρ)
  let : FiniteDimensional E (C.sc' n (n + 1) (n + 2)).X₂ := by
    change FiniteDimensional E ((Fin (n + 1) → G) → V)
    infer_instance
  let : FiniteDimensional E (C.sc' n (n + 1) (n + 2)).homology :=
    finiteDimensional_shortComplex_homology _
  exact FiniteDimensional.of_injective
    (C.homologyIsoSc' n (n + 1) (n + 2) (by simp) (by simp)).hom.hom
    (C.homologyIsoSc' n (n + 1) (n + 2) (by simp) (by simp)).toLinearEquiv.injective

/-- The ordinary positive-degree cohomology dimension is determined by two kernels. -/
theorem finrank_groupCohomology_add_finrank_cochains (ρ : Representation E G V) (n : ℕ) :
    Module.finrank E (groupCohomology (Rep.of ρ) (n + 1)) +
      Module.finrank E ((Fin n → G) → V) =
        Module.finrank E (LinearMap.ker (differential ρ (n + 1))) +
          Module.finrank E (LinearMap.ker (differential ρ n)) := by
  let C := groupCohomology.inhomogeneousCochains (Rep.of ρ)
  let : FiniteDimensional E (C.sc' n (n + 1) (n + 2)).X₁ := by
    change FiniteDimensional E ((Fin n → G) → V)
    infer_instance
  let : FiniteDimensional E (C.sc' n (n + 1) (n + 2)).X₂ := by
    change FiniteDimensional E ((Fin (n + 1) → G) → V)
    infer_instance
  have h := finrank_homology_add_finrank_source (C.sc' n (n + 1) (n + 2))
  have he := (C.homologyIsoSc' n (n + 1) (n + 2) (by simp) (by simp)).toLinearEquiv.finrank_eq
  rw [← he] at h
  change Module.finrank E (C.homology (n + 1)) +
    Module.finrank E ((Fin n → G) → V) =
      Module.finrank E (LinearMap.ker (C.d (n + 1) (n + 2)).hom) +
        Module.finrank E (LinearMap.ker (C.d n (n + 1)).hom) at h
  have hd (j : ℕ) : C.d j (j + 1) = inhomogeneousCochains.d (Rep.of ρ) j :=
    groupCohomology.inhomogeneousCochains.d_def (Rep.of ρ) j
  rw [hd (n + 1), hd n] at h
  exact h

/-- Field extension preserves actual ordinary cohomology dimensions in every positive degree. -/
theorem finrank_groupCohomology_baseChange (ρ : Representation E G V) (n : ℕ) :
    Module.finrank L (groupCohomology (Rep.of (baseChange L ρ)) (n + 1)) =
      Module.finrank E (groupCohomology (Rep.of ρ) (n + 1)) := by
  have hE := finrank_groupCohomology_add_finrank_cochains ρ n
  have hL := finrank_groupCohomology_add_finrank_cochains (baseChange L ρ) n
  rw [finrank_cochains, finrank_ker_differential, finrank_ker_differential] at hL
  omega

theorem finrank_H1_baseChange (ρ : Representation E G V) :
    Module.finrank L (groupCohomology (Rep.of (baseChange L ρ)) 1) =
      Module.finrank E (groupCohomology (Rep.of ρ) 1) :=
  finrank_groupCohomology_baseChange ρ 0

theorem finrank_H2_baseChange (ρ : Representation E G V) :
    Module.finrank L (groupCohomology (Rep.of (baseChange L ρ)) 2) =
      Module.finrank E (groupCohomology (Rep.of ρ) 2) :=
  finrank_groupCohomology_baseChange ρ 1

end Cochains
end Kourovka2135.GroupCohomologyFieldExtension
