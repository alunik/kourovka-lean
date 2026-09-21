import Kourovka2135.SLTwoHomogeneousFunctions
import Kourovka2135.BinaryTensorSLTwoWeyl

/-! Concrete fixed vectors in homogeneous-function principal series.

Upper-unipotent invariants are the two coordinate lines, with their actual
opposite torus weights. These facts refer to the constructed SL2 action and
do not assume a classification or irreducibility statement.
-/

set_option autoImplicit false
noncomputable section
universe u v

namespace Kourovka2135.SLTwoPrincipalSeries

open SLTwoHomogeneousFunctions

variable (k : Type u) [Field k] {F : Type v} [Field F] (σ : F →+* k) (n : ℕ)

attribute [local instance] Classical.propDecidable

/-- One on the affine chart and zero at infinity. -/
def affineIndicator : Carrier k σ n := (coordinates k σ n).symm (0, fun _ => 1)

/-- The coordinate delta vector at infinity. -/
def infinityDelta : Carrier k σ n := (coordinates k σ n).symm (1, fun _ => 0)

/-- The coordinate delta vector at an affine parameter. -/
def affineDelta (t : F) : Carrier k σ n := by
  classical
  exact (coordinates k σ n).symm (0, Pi.single t 1)

@[simp] theorem coordinates_affineIndicator :
    coordinates k σ n (affineIndicator k σ n) = (0, fun _ => 1) :=
  (coordinates k σ n).apply_symm_apply _

@[simp] theorem coordinates_infinityDelta :
    coordinates k σ n (infinityDelta k σ n) = (1, fun _ => 0) :=
  (coordinates k σ n).apply_symm_apply _

@[simp] theorem coordinates_affineDelta (t : F) :
    coordinates k σ n (affineDelta k σ n t) = (0, Pi.single t 1) :=
  (coordinates k σ n).apply_symm_apply _

theorem affineIndicator_ne_zero : affineIndicator k σ n ≠ 0 := by
  intro h
  have hh := congrArg (fun p : k × (F → k) => p.2 0)
    (congrArg (coordinates k σ n) h)
  rw [coordinates_affineIndicator, map_zero] at hh
  exact one_ne_zero hh

theorem infinityDelta_ne_zero : infinityDelta k σ n ≠ 0 := by
  intro h
  have hh := congrArg (fun p : k × (F → k) => p.1)
    (congrArg (coordinates k σ n) h)
  rw [coordinates_infinityDelta, map_zero] at hh
  exact one_ne_zero hh

/-- The two coordinate lines are distinct over every coefficient field. -/
theorem infinityDelta_ne_smul_affineIndicator (a : k) :
    infinityDelta k σ n ≠ a • affineIndicator k σ n := by
  intro h
  have hh := congrArg (fun p : k × (F → k) => p.1)
    (congrArg (coordinates k σ n) h)
  rw [coordinates_infinityDelta, map_smul, coordinates_affineIndicator] at hh
  change (1 : k) = a • (0 : k) at hh
  rw [smul_zero] at hh
  exact one_ne_zero hh

theorem unipotent_affineIndicator (t : F) :
    representation k σ n (SLTwo.uni t) (affineIndicator k σ n) =
      affineIndicator k σ n := by
  apply (coordinates k σ n).injective
  rw [coordinates_uni, coordinates_affineIndicator]

theorem unipotent_infinityDelta (t : F) :
    representation k σ n (SLTwo.uni t) (infinityDelta k σ n) =
      infinityDelta k σ n := by
  apply (coordinates k σ n).injective
  rw [coordinates_uni, coordinates_infinityDelta]

/-- All actual upper-unipotent fixed vectors lie in the two displayed lines. -/
theorem unipotent_fixed_iff (h : Carrier k σ n) :
    (∀ t : F, representation k σ n (SLTwo.uni t) h = h) ↔
      ∃ a b : k, h = a • affineIndicator k σ n + b • infinityDelta k σ n := by
  constructor
  · intro hh
    have hconst (t : F) : (coordinates k σ n h).2 t = (coordinates k σ n h).2 0 := by
      have he := congrArg (fun x => (coordinates k σ n x).2 0) (hh t)
      simpa only [coordinates_uni, zero_add] using he
    refine ⟨(coordinates k σ n h).2 0, (coordinates k σ n h).1, ?_⟩
    apply (coordinates k σ n).injective
    rw [map_add, map_smul, map_smul, coordinates_affineIndicator,
      coordinates_infinityDelta]
    apply Prod.ext
    · simp
    · funext t
      simpa using hconst t
  · rintro ⟨a, b, rfl⟩ t
    rw [map_add, map_smul, map_smul, unipotent_affineIndicator,
      unipotent_infinityDelta]

/-- The affine invariant line has the positive homogeneous torus weight. -/
theorem torus_affineIndicator (r : Fˣ) :
    representation k σ n (SLTwo.tor r) (affineIndicator k σ n) =
      σ (r : F) ^ n • affineIndicator k σ n := by
  apply (coordinates k σ n).injective
  rw [coordinates_tor, map_smul, coordinates_affineIndicator]
  ext t <;> simp

/-- The infinity invariant line has the inverse homogeneous torus weight. -/
theorem torus_infinityDelta (r : Fˣ) :
    representation k σ n (SLTwo.tor r) (infinityDelta k σ n) =
      σ ((r⁻¹ : Fˣ) : F) ^ n • infinityDelta k σ n := by
  apply (coordinates k σ n).injective
  rw [coordinates_tor, map_smul, coordinates_infinityDelta]
  ext t <;> simp

end Kourovka2135.SLTwoPrincipalSeries
