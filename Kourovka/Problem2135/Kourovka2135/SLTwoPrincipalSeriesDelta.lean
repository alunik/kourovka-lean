import Kourovka2135.SLTwoPrincipalSeries

/-! Coordinate deltas and cyclic generation of homogeneous-function modules.

The infinity delta has a genuine Weyl translate at affine zero, and actual
upper unipotents reach every affine delta. Thus its orbit spans the entire
finite-parameter function module. No simplicity statement is assumed.
-/

set_option autoImplicit false
noncomputable section
universe u v

namespace Kourovka2135.SLTwoPrincipalSeries

open SLTwoHomogeneousFunctions
open scoped CharTwo

variable (k : Type u) [Field k] {F : Type v} [Field F] (σ : F →+* k) (n : ℕ)

attribute [local instance] Classical.propDecidable

theorem affineIndicator_apply (z : Point F) :
    affineIndicator k σ n z = if z.val 0 = 0 then 0 else σ (z.val 0) ^ n := by
  change reconstruct k σ n (0, fun _ => 1) z = _
  simp [reconstruct]

theorem infinityDelta_apply (z : Point F) :
    infinityDelta k σ n z = if z.val 0 = 0 then σ (z.val 1) ^ n else 0 := by
  change reconstruct k σ n (1, fun _ => 0) z = _
  simp [reconstruct]

/-- Upper unipotents move the affine delta by the actual translation convention. -/
theorem unipotent_affineDelta (b t : F) :
    representation k σ n (SLTwo.uni b) (affineDelta k σ n t) =
      affineDelta k σ n (t - b) := by
  apply (coordinates k σ n).injective
  rw [coordinates_uni, coordinates_affineDelta, coordinates_affineDelta]
  apply Prod.ext
  · rfl
  · funext s
    simp [Pi.single_apply, eq_sub_iff_add_eq]

section CharTwo

variable [CharP k 2]

/-- The actual determinant-one Weyl matrix sends infinity delta to affine zero. -/
theorem weyl_infinityDelta :
    representation k σ n (SLTwo.weyl F) (infinityDelta k σ n) =
      affineDelta k σ n 0 := by
  apply (coordinates k σ n).injective
  rw [coordinates_affineDelta]
  apply Prod.ext
  · change infinityDelta k σ n (pointAction (SLTwo.weyl F) (infinity F)) = 0
    rw [infinityDelta_apply]
    simp [pointAction, infinity, SLTwo.weyl_val]
  · funext t
    change infinityDelta k σ n (pointAction (SLTwo.weyl F) (affine t)) =
      (Pi.single (0 : F) (1 : k) : F → k) t
    rw [infinityDelta_apply]
    by_cases ht : t = 0
    · subst t
      simp [pointAction, affine, SLTwo.weyl_val, CharTwo.neg_eq]
    · simp [pointAction, affine, SLTwo.weyl_val, ht]

end CharTwo

section Finite

variable [Fintype F]

/-- The two projective charts give the explicit finite coordinate expansion. -/
theorem coordinate_expansion (h : Carrier k σ n) :
    h = (coordinates k σ n h).1 • infinityDelta k σ n +
      ∑ t : F, (coordinates k σ n h).2 t • affineDelta k σ n t := by
  apply (coordinates k σ n).injective
  rw [map_add, map_smul, map_sum, coordinates_infinityDelta]
  simp only [map_smul, coordinates_affineDelta]
  apply Prod.ext
  · simp [Prod.fst_sum]
  · funext t
    simp [Prod.snd_sum, Finset.sum_apply, Pi.single_apply]

variable [CharP k 2]

/-- Every SL2-stable subspace containing infinity delta is the entire module. -/
theorem eq_top_of_infinityDelta_mem (W : Submodule k (Carrier k σ n))
    (hstable : ∀ (g : SLTwo.SL2 F) (h : Carrier k σ n), h ∈ W →
      representation k σ n g h ∈ W)
    (hD : infinityDelta k σ n ∈ W) : W = ⊤ := by
  have hzero : affineDelta k σ n (0 : F) ∈ W := by
    have h := hstable (SLTwo.weyl F) _ hD
    rwa [weyl_infinityDelta] at h
  have hdelta (t : F) : affineDelta k σ n t ∈ W := by
    have h := hstable (SLTwo.uni (-t)) _ hzero
    simpa only [unipotent_affineDelta, zero_sub, neg_neg] using h
  apply le_antisymm le_top
  intro h _
  rw [coordinate_expansion k σ n h]
  exact W.add_mem (W.smul_mem _ hD)
    (W.sum_mem (fun t _ => W.smul_mem _ (hdelta t)))

end Finite

end Kourovka2135.SLTwoPrincipalSeries
