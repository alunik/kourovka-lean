import Kourovka2135.CocycleGeneratorBounds

/-! One-cocycles normalized on an actual subgroup.

The actual cohomology projection is injective on normalized cocycles when the
subgroup has no fixed vectors, and surjective when its actual first cohomology
vanishes. No finiteness or finite-dimensionality assumption is used.
-/

set_option autoImplicit false
noncomputable section
universe u

namespace Kourovka2135.NormalizedCocycleSubspace

open groupCohomology CategoryTheory CocycleGeneratorBounds

variable {k G V : Type u} [Field k] [Group G]
variable [AddCommGroup V] [Module k V]
variable (ρ : Representation k G V) (B : Subgroup G)

/-- Restriction of an actual one-cocycle to the subgroup. -/
def restriction : cocycles₁ (Rep.of ρ) →ₗ[k]
    cocycles₁ (Rep.of (ρ.comp B.subtype)) where
  toFun z := ⟨fun b => z b, (mem_cocycles₁_iff _).mpr
    (fun a b => (mem_cocycles₁_iff z).mp z.property a b)⟩
  map_add' z w := by
    apply cocycles₁_ext
    intro b
    rfl
  map_smul' c z := by
    apply cocycles₁_ext
    intro b
    rfl

@[simp] theorem restriction_apply (z : cocycles₁ (Rep.of ρ)) (b : B) :
    restriction ρ B z b = z b := rfl

/-- The linear subspace of one-cocycles that vanish on the subgroup. -/
def normalized : Submodule k (cocycles₁ (Rep.of ρ)) where
  carrier := {z | ∀ b : B, z b = 0}
  zero_mem' _ := rfl
  add_mem' := by
    intro z w hz hw b
    change z b + w b = 0
    rw [hz b, hw b, zero_add]
  smul_mem' := by
    intro c z hz b
    change c • z b = 0
    rw [hz b, smul_zero]

@[simp] theorem mem_normalized (z : cocycles₁ (Rep.of ρ)) :
    z ∈ normalized ρ B ↔ ∀ b : B, z b = 0 := Iff.rfl

/-- The actual H1 projection, restricted to normalized cocycles. -/
def cohomologyProjection : normalized ρ B →ₗ[k] groupCohomology (Rep.of ρ) 1 :=
  (H1π (Rep.of ρ)).hom.comp (normalized ρ B).subtype

@[simp] theorem cohomologyProjection_apply (z : normalized ρ B) :
    cohomologyProjection ρ B z = H1π (Rep.of ρ) z.val := rfl

/-- A normalized principal cocycle is zero when the subgroup fixes no vector. -/
theorem cohomologyProjection_injective
    (hfixed : Representation.invariants (ρ.comp B.subtype) = ⊥) :
    Function.Injective (cohomologyProjection ρ B) := by
  intro z w he
  have hzrange : z.val - w.val ∈ LinearMap.range (principal ρ) := by
    rw [← cohomology_projection_ker]
    change (H1π (Rep.of ρ)).hom (z.val - w.val) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr he
  obtain ⟨v, hv⟩ := hzrange
  have hvinv : v ∈ Representation.invariants (ρ.comp B.subtype) := by
    intro b
    have hb := congrArg (fun a : cocycles₁ (Rep.of ρ) => a b) hv
    change ρ b v - v = z.val b - w.val b at hb
    rw [z.property b, w.property b, sub_self] at hb
    exact sub_eq_zero.mp hb
  have hvzero : v = 0 := by
    rw [hfixed] at hvinv
    exact hvinv
  apply Subtype.ext
  apply sub_eq_zero.mp
  rw [← hv, hvzero, map_zero]

/-- Vanishing of subgroup H1 permits normalization of every global class. -/
theorem cohomologyProjection_surjective
    (hvanish : Subsingleton (groupCohomology (Rep.of (ρ.comp B.subtype)) 1)) :
    Function.Surjective (cohomologyProjection ρ B) := by
  let := hvanish
  intro x
  have hsurj : Function.Surjective (H1π (Rep.of ρ)) :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  obtain ⟨z, rfl⟩ := hsurj x
  have hrzero : H1π (Rep.of (ρ.comp B.subtype)) (restriction ρ B z) = 0 :=
    Subsingleton.elim _ _
  have hrrange : restriction ρ B z ∈ LinearMap.range (principal (ρ.comp B.subtype)) := by
    rw [← cohomology_projection_ker]
    exact hrzero
  obtain ⟨v, hv⟩ := hrrange
  let zn : normalized ρ B := ⟨z - principal ρ v, by
    intro b
    have hb := congrArg
      (fun w : cocycles₁ (Rep.of (ρ.comp B.subtype)) => w b) hv
    change ρ b v - v = z b at hb
    change z b - (ρ b v - v) = 0
    exact sub_eq_zero.mpr hb.symm⟩
  refine ⟨zn, ?_⟩
  have hpzero : (H1π (Rep.of ρ)).hom (principal ρ v) = 0 := by
    have hp : principal ρ v ∈ LinearMap.ker (H1π (Rep.of ρ)).hom := by
      rw [cohomology_projection_ker]
      exact ⟨v, rfl⟩
    exact hp
  change (H1π (Rep.of ρ)).hom (z - principal ρ v) = (H1π (Rep.of ρ)).hom z
  rw [map_sub, hpzero, sub_zero]

/-- Actual normalized cocycles and actual H1 are linearly equivalent under the
two separate subgroup hypotheses. -/
def cohomologyEquiv
    (hfixed : Representation.invariants (ρ.comp B.subtype) = ⊥)
    (hvanish : Subsingleton (groupCohomology (Rep.of (ρ.comp B.subtype)) 1)) :
    normalized ρ B ≃ₗ[k] groupCohomology (Rep.of ρ) 1 :=
  LinearEquiv.ofBijective (cohomologyProjection ρ B)
    ⟨cohomologyProjection_injective ρ B hfixed,
      cohomologyProjection_surjective ρ B hvanish⟩

@[simp] theorem cohomologyEquiv_apply
    (hfixed : Representation.invariants (ρ.comp B.subtype) = ⊥)
    (hvanish : Subsingleton (groupCohomology (Rep.of (ρ.comp B.subtype)) 1))
    (z : normalized ρ B) :
    cohomologyEquiv ρ B hfixed hvanish z = H1π (Rep.of ρ) z.val := rfl

end Kourovka2135.NormalizedCocycleSubspace
