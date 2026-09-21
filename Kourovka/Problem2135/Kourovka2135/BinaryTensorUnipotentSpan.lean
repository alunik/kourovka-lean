import Kourovka2135.BinaryTensorSLTwoAction
import Kourovka2135.BinaryExteriorGroupAlgebra
import Kourovka2135.BinaryExteriorAugmentation

/-! The actual upper-unipotent operators span the squarefree algebra action.

The proved finite-field group-algebra equivalence supplies the span; neither
irreducibility nor a classification of representations is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.BinaryTensorUnipotentSpan

open scoped IsMulCommutative

variable (k : Type*) [Field k] [CharP k 2] {f : ℕ} (I : Finset (Fin f))
variable {F : Type*} [Field F] [Fintype F] (σ : F →+* k)
variable (hcard : Fintype.card F = 2 ^ f)

include hcard

/-- A subspace stable under all actual upper unipotents is stable under every
element of their concrete squarefree algebra. -/
theorem exterior_smul_mem (W : Submodule k (BinaryTensorCoefficient.Carrier k I))
    (hW : ∀ (t : F) (v : BinaryTensorCoefficient.Carrier k I), v ∈ W →
      BinaryTensorSLTwo.representation k σ I (SLTwo.uni t) v ∈ W)
    (a : BinaryExteriorAlgebra.Carrier k f)
    (v : BinaryTensorCoefficient.Carrier k I) (hv : v ∈ W) : a • v ∈ W := by
  obtain ⟨z, rfl⟩ := (BinaryExteriorGroupAlgebra.equivalence k f σ hcard).surjective a
  induction z using AddMonoidAlgebra.induction_linear with
  | zero => simpa only [map_zero, zero_smul] using W.zero_mem
  | add z w hz hw =>
      simpa only [map_add, add_smul] using W.add_mem hz hw
  | single t c =>
      rw [BinaryExteriorGroupAlgebra.equivalence_single, smul_assoc,
        ← BinaryTensorSLTwo.representation_uni k I σ t v]
      exact W.smul_mem c (hW t v hv)

/-- Every included square-zero generator preserves an upper-unipotent-stable subspace. -/
theorem generator_mul_mem (W : Submodule k (BinaryTensorCoefficient.Carrier k I))
    (hW : ∀ (t : F) (v : BinaryTensorCoefficient.Carrier k I), v ∈ W →
      BinaryTensorSLTwo.representation k σ I (SLTwo.uni t) v ∈ W)
    (i : I) (v : BinaryTensorCoefficient.Carrier k I) (hv : v ∈ W) :
    BinaryTensorCoefficient.generator k I i * v ∈ W := by
  have h := exterior_smul_mem k I σ hcard W hW
    (BinaryExteriorAlgebra.generator k f i) v hv
  rwa [BinaryTensorCoefficient.smul_eq,
    BinaryTensorCoefficient.projection_generator_of_mem k I i i.property] at h

/-- On a vector fixed by all actual upper unipotents, the algebra acts through
its actual augmentation character. -/
theorem exterior_smul_of_unipotent_fixed (v : BinaryTensorCoefficient.Carrier k I)
    (hv : ∀ t : F, BinaryTensorSLTwo.representation k σ I (SLTwo.uni t) v = v)
    (a : BinaryExteriorAlgebra.Carrier k f) :
    a • v = BinaryExteriorAugmentation.augmentation k f a • v := by
  obtain ⟨z, rfl⟩ := (BinaryExteriorGroupAlgebra.equivalence k f σ hcard).surjective a
  induction z using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add z w hz hw => simp only [map_add, add_smul, hz, hw]
  | single t c =>
      rw [BinaryExteriorGroupAlgebra.equivalence_single, smul_assoc,
        ← BinaryTensorSLTwo.representation_uni k I σ t v, hv t]
      simp only [map_smul, BinaryExteriorAugmentation.augmentation_character,
        smul_eq_mul, mul_one]

theorem generator_mul_eq_zero_of_unipotent_fixed
    (v : BinaryTensorCoefficient.Carrier k I)
    (hv : ∀ t : F, BinaryTensorSLTwo.representation k σ I (SLTwo.uni t) v = v)
    (i : I) : BinaryTensorCoefficient.generator k I i * v = 0 := by
  have h := exterior_smul_of_unipotent_fixed k I σ hcard v hv
    (BinaryExteriorAlgebra.generator k f i)
  simpa only [BinaryTensorCoefficient.smul_eq,
    BinaryTensorCoefficient.projection_generator_of_mem k I i i.property,
    BinaryExteriorAugmentation.augmentation_generator, zero_smul] using h

end Kourovka2135.BinaryTensorUnipotentSpan
