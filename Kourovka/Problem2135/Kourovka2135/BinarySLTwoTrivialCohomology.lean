import Kourovka2135.BinaryTrivialH2Weights
import Kourovka2135.BinaryTensorSLTwoCohomology
import Kourovka2135.SLTwoFullTensorEvaluation

/-! Actual ordinary H2 vanishing for scalar trivial coefficients on binary
SL2 in extension degree at least three. The proof uses the checked tensor
resolution, its actual torus action, restriction to the upper unipotent
subgroup, and the actual empty-tensor equivalence with scalar coefficients.
No group-extension splitting theorem is asserted here. -/

set_option autoImplicit false
noncomputable section
universe u

namespace Kourovka2135.BinarySLTwoTrivialCohomology

open CategoryTheory BinaryTensorSLTwoRestriction

variable (k : Type u) [Field k] [CharP k 2]
variable {F : Type u} [Field F] (σ : F →+* k) (f : ℕ)

/-- The checked empty-tensor equivalence transports ordinary cohomology to
the actual scalar trivial representation in every degree. -/
def emptyTrivialCohomologyIso (n : ℕ) :
    groupCohomology (ambient k (∅ : Finset (Fin f)) σ) n ≅
      groupCohomology (Rep.of (Representation.trivial k (SLTwo.SL2 F) k)) n :=
  groupCohomology.mapIso (MulEquiv.refl (SLTwo.SL2 F))
    (SLTwoFullTensorEvaluation.emptyTrivialEquiv k σ f).toLinearEquiv
    (fun g => (SLTwoFullTensorEvaluation.emptyTrivialEquiv k σ f).isIntertwining' g) n

variable [Fintype F] (hcard : Fintype.card F = 2 ^ f)

/-- No actual ordinary additive-group H2 class is fixed by a primitive torus
element when the coefficient is the empty tensor and f is at least three. -/
theorem additive_fixed_H2_eq_bot (r : Fˣ)
    (hr : orderOf (Units.map σ.toMonoidHom r) = 2 ^ f - 1) (hf : 3 ≤ f) :
    ((BinaryAdditiveTorusAction.cohomologyMap k (∅ : Finset (Fin f)) σ hcard r 2).hom -
      LinearMap.id).ker = ⊥ :=
  BinaryTrivialH2Weights.fixedSpace_eq_bot k (Units.map σ.toMonoidHom r) hr hf
    (BinaryAdditiveTorusAction.cohomologyMap k ∅ σ hcard r 2).hom
    (BinaryAdditiveTorusBounds.coordinate k ∅ σ hcard 1)
    (BinaryAdditiveTorusBounds.coordinate_injective k ∅ σ hcard 1)
    (BinaryAdditiveTorusBounds.coordinate_cohomologyMap k ∅ σ hcard r 1)

include hcard in
/-- The actual empty-tensor SL2 cohomology has H2 dimension zero for f ≥ 3. -/
theorem finrank_empty_H2_eq_zero (hf : 3 ≤ f) :
    Module.finrank k (groupCohomology (ambient k (∅ : Finset (Fin f)) σ) 2) = 0 := by
  obtain ⟨r, hr⟩ := BinaryAdditiveTorusBounds.exists_primitive k σ hcard
  have h := BinaryTensorSLTwoCohomology.finrank_le_fixed k ∅ σ hcard r 1 (Or.inr rfl)
  rw [additive_fixed_H2_eq_bot k σ f hcard r hr hf] at h
  exact Nat.eq_zero_of_le_zero (by simpa using h)

include hcard in
/-- Actual H2 vanishing for the empty tensor, with finiteness discharged. -/
theorem subsingleton_empty_H2 (hf : 3 ≤ f) :
    Subsingleton (groupCohomology (ambient k (∅ : Finset (Fin f)) σ) 2) := by
  have := BinaryTensorSLTwoCohomology.finiteDimensional_ambient k ∅ σ hcard 1
  exact Module.finrank_zero_iff.mp (finrank_empty_H2_eq_zero k σ f hcard hf)

include σ hcard in
/-- Ordinary H2 of SL2(2^f) with actual scalar trivial coefficients vanishes
for f ≥ 3 over every characteristic-two field containing the parameter field. -/
theorem subsingleton_trivial_H2 (hf : 3 ≤ f) :
    Subsingleton
      (groupCohomology (Rep.of (Representation.trivial k (SLTwo.SL2 F) k)) 2) := by
  let := subsingleton_empty_H2 k σ f hcard hf
  exact (emptyTrivialCohomologyIso k σ f 2).toLinearEquiv.symm.injective.subsingleton

include σ hcard in
/-- The scalar-trivial vanishing theorem also gives an exact dimension statement. -/
theorem finrank_trivial_H2_eq_zero (hf : 3 ≤ f) :
    Module.finrank k
      (groupCohomology (Rep.of (Representation.trivial k (SLTwo.SL2 F) k)) 2) = 0 := by
  let := subsingleton_trivial_H2 k σ f hcard hf
  exact Module.finrank_zero_of_subsingleton

end Kourovka2135.BinarySLTwoTrivialCohomology
