import Kourovka2135.BinaryTensorSLTwoCohomologyTransfer

/-! Positive-degree cohomology of the full-support binary tensor module vanishes.
The explicit surviving-coordinate injection has empty target coordinates;
odd-index restriction transports this calculation to SL2. -/

set_option autoImplicit false
noncomputable section
universe u

namespace Kourovka2135.BinarySteinbergCohomology

open CategoryTheory BinaryCochainGraded BinaryAdditiveCohomology
open BinaryTensorSLTwoRestriction BinaryTensorSLTwoCohomology

variable (k : Type u) [Field k] [CharP k 2] {f : ℕ}
variable {F : Type u} [Field F] [Fintype F] (σ : F →+* k)
variable (hcard : Fintype.card F = 2 ^ f)

theorem survivorIndex_univ_isEmpty (n : ℕ) :
    IsEmpty (SurvivorIndex (Finset.univ : Finset (Fin f)) (n + 1)) := by
  classical
  refine ⟨fun a => ?_⟩
  have hz : a.val.val = 0 := by
    ext i
    exact a.property i (Finset.mem_univ i)
  have hd := a.val.property
  rw [hz] at hd
  simp only [map_zero] at hd
  omega

/-- The full-support tensor has no surviving positive-degree root coordinates. -/
theorem subsingleton_additive (n : ℕ) :
    Subsingleton (groupCohomology
      (coefficientRepresentation k (Finset.univ : Finset (Fin f)) σ hcard) (n + 1)) := by
  let : IsEmpty (SurvivorIndex (Finset.univ : Finset (Fin f)) (n + 1)) :=
    survivorIndex_univ_isEmpty n
  exact (BinaryAdditiveCohomologyDimension.coordinates_injective
    k Finset.univ σ hcard n).subsingleton

include hcard in
/-- Actual positive-degree SL2 cohomology of the Steinberg tensor vanishes. -/
theorem subsingleton_ambient (n : ℕ) :
    Subsingleton (groupCohomology
      (ambient k (Finset.univ : Finset (Fin f)) σ) (n + 1)) := by
  have : CharP F 2 := (σ.charP_iff_charP 2).mpr inferInstance
  let : Subsingleton (groupCohomology
      (coefficientRepresentation k (Finset.univ : Finset (Fin f)) σ hcard) (n + 1)) :=
    subsingleton_additive k σ hcard n
  let : Subsingleton (groupCohomology
      (Rep.res (SLTwo.Unip F).subtype (ambient k (Finset.univ : Finset (Fin f)) σ))
      (n + 1)) :=
    (cohomologyIso k Finset.univ σ hcard (n + 1)).toLinearEquiv.injective.subsingleton
  exact (GroupCohomology.restriction_injective_of_odd_index (SLTwo.Unip F)
    (ambient k (Finset.univ : Finset (Fin f)) σ) (n + 1) SLTwo.odd_index_unip).subsingleton

end Kourovka2135.BinarySteinbergCohomology
