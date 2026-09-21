import Kourovka2135.SLTwoAugmentationSocle
import Kourovka2135.IrreducibleImageComparison

/-! The zero-weight alternative for an irreducible source.

The actual augmentation either identifies the source with the scalar trivial
representation, or its image is the actual augmentation kernel.
-/

set_option autoImplicit false
noncomputable section
universe u v w

namespace Kourovka2135.SLTwoZeroWeightClassification

open SLTwoHomogeneousFunctions SLTwoPrincipalSeries

variable (k : Type u) [Field k]
variable {F : Type v} [Field F] [Fintype F] (σ : F →+* k)

/-- The full-group invariant augmentation is an actual intertwining map. -/
def augmentationIntertwiner :
    (representation k σ 0).IntertwiningMap (Representation.trivial k (SLTwo.SL2 F) k) :=
  (augmentation k σ).intertwiningMap_of_isIntertwiningMap _ _
    (fun g h => augmentation_action k σ g h)

variable {V : Type w} [AddCommGroup V] [Module k V]
variable (ρ : Representation k (SLTwo.SL2 F) V) [ρ.IsIrreducible]

omit [Fintype F] in
/-- A nonzero map from an irreducible representation to the scalar trivial
representation is an actual equivalence, with no finite-dimensionality premise. -/
def equivScalarOfNonzero
    (l : ρ.IntertwiningMap (Representation.trivial k (SLTwo.SL2 F) k))
    (hl : l ≠ 0) : ρ.Equiv (Representation.trivial k (SLTwo.SL2 F) k) := by
  have hi := (Representation.IsIrreducible.injective_or_eq_zero l).resolve_right hl
  have hl' : l.toLinearMap ≠ 0 := by
    intro h
    apply hl
    apply Representation.IntertwiningMap.ext
    exact h
  have hs := (LinearMap.surjective_or_eq_zero l.toLinearMap).resolve_right hl'
  exact l.ofBijective ⟨hi, hs⟩

variable [CharP k 2]

omit [ρ.IsIrreducible] in
/-- If the augmentation kills a nonzero image, that image is
exactly the augmentation kernel. -/
theorem range_eq_ker_of_augmentation_zero
    (j : ρ.IntertwiningMap (representation k σ 0)) (hj : j ≠ 0)
    (haug : (augmentationIntertwiner k σ).comp j = 0) :
    j.range.toSubmodule = LinearMap.ker (augmentation k σ) := by
  have hW : j.range.toSubmodule ≠ ⊥ := by
    intro h
    apply hj
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    have hv : j v ∈ j.range.toSubmodule := ⟨v, rfl⟩
    rw [h] at hv
    exact hv
  apply eq_augmentation_ker_of_ne_bot k σ j.range.toSubmodule hW
  · rintro _ ⟨v, rfl⟩
    have h := congrArg (fun l : ρ.IntertwiningMap
      (Representation.trivial k (SLTwo.SL2 F) k) => l v) haug
    exact h
  · intro g h hh
    exact j.range.apply_mem_toSubmodule g hh

/-- The scalar branch and the augmentation-kernel branch exhaust weight zero. -/
theorem scalar_equiv_or_range_eq_ker
    (j : ρ.IntertwiningMap (representation k σ 0)) (hj : j ≠ 0) :
    Nonempty (ρ.Equiv (Representation.trivial k (SLTwo.SL2 F) k)) ∨
      j.range.toSubmodule = LinearMap.ker (augmentation k σ) := by
  classical
  by_cases haug : (augmentationIntertwiner k σ).comp j = 0
  · exact Or.inr (range_eq_ker_of_augmentation_zero k σ ρ j hj haug)
  · exact Or.inl ⟨equivScalarOfNonzero k ρ ((augmentationIntertwiner k σ).comp j) haug⟩

end Kourovka2135.SLTwoZeroWeightClassification
