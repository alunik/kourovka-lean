import Kourovka2135.SLTwoHomogeneousWeightEquiv
import Kourovka2135.SLTwoPrincipalSeries
import Kourovka2135.BinaryTensorSLTwoEvaluation

/-! Full and empty binary tensor models inside homogeneous weight zero.

The full tensor is transported through the identity-on-functions change of
weight `2^f - 1` to zero. Its top vector remains the affine indicator. The
empty tensor also maps to weight zero and is explicitly equivalent to the
trivial scalar representation through the genuine empty tensor product.
-/

set_option autoImplicit false
noncomputable section
universe u v

namespace Kourovka2135.SLTwoFullTensorEvaluation

open BinaryTensorSubsetBasis
open scoped TensorProduct PiTensorProduct

/-- The full binary subset has the full multiplicative-field weight. -/
theorem subsetWeight_univ (f : ℕ) :
    BinaryExteriorGroupAlgebra.subsetWeight f (Finset.univ : Finset (Fin f)) = 2 ^ f - 1 := by
  unfold BinaryExteriorGroupAlgebra.subsetWeight
  induction f with
  | zero => simp
  | succ f ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [ih, pow_succ]
      have hpos : 0 < 2 ^ f := by positivity
      omega

@[simp] theorem subsetWeight_empty (f : ℕ) :
    BinaryExteriorGroupAlgebra.subsetWeight f (∅ : Finset (Fin f)) = 0 := by
  simp [BinaryExteriorGroupAlgebra.subsetWeight]

section Full
variable (k : Type u) [Field k] [CharP k 2]
variable {F : Type v} [Field F] [Fintype F] (σ : F →+* k)
variable (f : ℕ) (hcard : Fintype.card F = 2 ^ f)

omit [CharP k 2] in
/-- Actual equivalence from the full binary homogeneous weight to weight zero. -/
def fullWeightEquiv : Representation.Equiv
    (SLTwoHomogeneousFunctions.representation k σ
      (BinaryExteriorGroupAlgebra.subsetWeight f (Finset.univ : Finset (Fin f))))
    (SLTwoHomogeneousFunctions.representation k σ 0) :=
  SLTwoHomogeneousWeightEquiv.equiv k σ _ 0 (by
    intro a
    rw [subsetWeight_univ, ← hcard]
    exact SLTwoHomogeneousWeightEquiv.unit_pow_card_sub_one k σ a)

omit [CharP k 2] in
@[simp] theorem fullWeightEquiv_apply
    (h : SLTwoHomogeneousFunctions.Carrier k σ
      (BinaryExteriorGroupAlgebra.subsetWeight f (Finset.univ : Finset (Fin f))))
    (z : SLTwoHomogeneousFunctions.Point F) :
    fullWeightEquiv k σ f hcard h z = h z := rfl

/-- The actual full-support tensor maps into the actual weight-zero representation. -/
def fullEvaluation : Representation.IntertwiningMap
    (BinaryTensorSLTwo.representation k σ (Finset.univ : Finset (Fin f)))
    (SLTwoHomogeneousFunctions.representation k σ 0) :=
  (fullWeightEquiv k σ f hcard).toIntertwiningMap.comp
    (BinaryTensorSLTwoEvaluation.evaluation k σ Finset.univ)

@[simp] theorem fullEvaluation_apply
    (v : BinaryTensorCoefficient.Carrier k (Finset.univ : Finset (Fin f)))
    (z : SLTwoHomogeneousFunctions.Point F) :
    fullEvaluation k σ f hcard v z =
      BinaryTensorSLTwoEvaluation.evaluationLinear k σ Finset.univ v z := rfl

/-- Identity-on-functions transport preserves the proved tensor injectivity. -/
theorem fullEvaluation_injective : Function.Injective (fullEvaluation k σ f hcard) := by
  intro v w hvw
  apply BinaryTensorSLTwoEvaluation.evaluation_injective k σ Finset.univ hcard
  apply (fullWeightEquiv k σ f hcard).toLinearEquiv.injective
  exact hvw

/-- The transported full tensor map is nonzero by evaluation at an affine point. -/
theorem fullEvaluation_ne_zero : fullEvaluation k σ f hcard ≠ 0 := by
  intro h
  have hz : fullEvaluation k σ f hcard (basis k Finset.univ (topIndex Finset.univ))
      (SLTwoHomogeneousFunctions.affine (0 : F)) = 0 := by
    rw [h]
    rfl
  rw [fullEvaluation_apply, BinaryTensorSLTwoEvaluation.evaluationLinear_top_affine] at hz
  exact one_ne_zero hz

/-- The full tensor top is the affine indicator, including the smallest field. -/
theorem fullEvaluation_top :
    fullEvaluation k σ f hcard (basis k Finset.univ (topIndex Finset.univ)) =
      SLTwoPrincipalSeries.affineIndicator k σ 0 := by
  have hw : 0 < BinaryExteriorGroupAlgebra.subsetWeight f
      (Finset.univ : Finset (Fin f)) := by
    rw [subsetWeight_univ, ← hcard]
    exact Nat.sub_pos_of_lt Fintype.one_lt_card
  apply (SLTwoHomogeneousFunctions.coordinates k σ 0).injective
  rw [SLTwoPrincipalSeries.coordinates_affineIndicator]
  apply Prod.ext
  · change fullEvaluation k σ f hcard (basis k Finset.univ (topIndex Finset.univ))
      (SLTwoHomogeneousFunctions.infinity F) = 0
    rw [fullEvaluation_apply]
    exact BinaryTensorSLTwoEvaluation.evaluationLinear_top_infinity k σ Finset.univ hw
  · funext t
    change fullEvaluation k σ f hcard (basis k Finset.univ (topIndex Finset.univ))
      (SLTwoHomogeneousFunctions.affine t) = 1
    rw [fullEvaluation_apply, BinaryTensorSLTwoEvaluation.evaluationLinear_top_affine]

/-- Coordinate form of the full top-vector formula. -/
theorem fullEvaluation_top_coordinates :
    SLTwoHomogeneousFunctions.coordinates k σ 0
      (fullEvaluation k σ f hcard (basis k Finset.univ (topIndex Finset.univ))) =
        (0, fun _ : F => 1) := by
  rw [fullEvaluation_top, SLTwoPrincipalSeries.coordinates_affineIndicator]

/-- The same top-vector formula in the native subtype-indexed exterior basis. -/
theorem fullEvaluation_top_native :
    fullEvaluation k σ f hcard
      (BinaryTensorCoefficient.basis k (Finset.univ : Finset (Fin f)) Finset.univ) =
        SLTwoPrincipalSeries.affineIndicator k σ 0 := by
  rw [← BinaryTensorSLTwoSimplicity.global_basis_top]
  exact fullEvaluation_top k σ f hcard

end Full

section Empty
variable (k : Type u) [Field k] [CharP k 2]
variable {F : Type v} [Field F] (σ : F →+* k) (f : ℕ)

omit [CharP k 2] in
/-- The empty support has zero homogeneous weight, with no field-size premise. -/
def emptyWeightEquiv : Representation.Equiv
    (SLTwoHomogeneousFunctions.representation k σ
      (BinaryExteriorGroupAlgebra.subsetWeight f (∅ : Finset (Fin f))))
    (SLTwoHomogeneousFunctions.representation k σ 0) :=
  SLTwoHomogeneousWeightEquiv.equiv k σ _ 0 (by intro a; rw [subsetWeight_empty])

/-- The genuine empty tensor also maps into the weight-zero representation. -/
def emptyEvaluation : Representation.IntertwiningMap
    (BinaryTensorSLTwo.representation k σ (∅ : Finset (Fin f)))
    (SLTwoHomogeneousFunctions.representation k σ 0) :=
  (emptyWeightEquiv k σ f).toIntertwiningMap.comp
    (BinaryTensorSLTwoEvaluation.evaluation k σ ∅)

@[simp] theorem emptyEvaluation_apply
    (v : BinaryTensorCoefficient.Carrier k (∅ : Finset (Fin f)))
    (z : SLTwoHomogeneousFunctions.Point F) :
    emptyEvaluation k σ f v z = BinaryTensorSLTwoEvaluation.evaluationLinear k σ ∅ v z := rfl

/-- The empty tensor top is the constant function one on all nonzero vectors. -/
theorem emptyEvaluation_top_apply (z : SLTwoHomogeneousFunctions.Point F) :
    emptyEvaluation k σ f (basis k ∅ (topIndex ∅)) z = 1 := by
  rw [emptyEvaluation_apply, BinaryTensorSLTwoEvaluation.evaluationLinear_top,
    subsetWeight_empty, pow_zero]

/-- The transported empty tensor map is nonzero. -/
theorem emptyEvaluation_ne_zero : emptyEvaluation k σ f ≠ 0 := by
  intro h
  have hz : emptyEvaluation k σ f (basis k ∅ (topIndex ∅))
      (SLTwoHomogeneousFunctions.affine (0 : F)) = 0 := by
    rw [h]
    rfl
  rw [emptyEvaluation_top_apply] at hz
  exact one_ne_zero hz

omit [CharP k 2] in
/-- The canonical empty tensor product is the scalar field. -/
def emptyScalarLinearEquiv : BinaryTensorCoefficient.Carrier k (∅ : Finset (Fin f)) ≃ₗ[k] k :=
  (BinaryTensorSLTwo.tensorEquiv k ∅).symm.trans
    (PiTensorProduct.isEmptyEquiv (∅ : Finset (Fin f)))

/-- There are no natural factors on which a matrix could act in the empty tensor. -/
theorem emptyTensorRepresentation (g : SLTwo.SL2 F) :
    BinaryTensorSLTwo.tensorRepresentation k σ (∅ : Finset (Fin f)) g = 1 := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  change BinaryTensorSLTwo.tensorRepresentation k σ (∅ : Finset (Fin f)) g
      (PiTensorProduct.tprod k x) = PiTensorProduct.tprod k x
  rw [BinaryTensorSLTwo.tensorRepresentation_tprod]
  congr 1
  funext i
  exact isEmptyElim i

/-- The transferred empty coefficient representation is also genuinely trivial. -/
theorem emptyRepresentation_apply (g : SLTwo.SL2 F)
    (v : BinaryTensorCoefficient.Carrier k (∅ : Finset (Fin f))) :
    BinaryTensorSLTwo.representation k σ ∅ g v = v := by
  rw [BinaryTensorSLTwo.representation_apply, emptyTensorRepresentation]
  exact (BinaryTensorSLTwo.tensorEquiv k ∅).apply_symm_apply v

/-- An actual equivalence from the empty model to the trivial scalar representation. -/
def emptyTrivialEquiv : Representation.Equiv
    (BinaryTensorSLTwo.representation k σ (∅ : Finset (Fin f)))
    (Representation.trivial k (SLTwo.SL2 F) k) :=
  Representation.Equiv.mk (emptyScalarLinearEquiv k f) (by
    intro g
    apply LinearMap.ext
    intro v
    change emptyScalarLinearEquiv k f (BinaryTensorSLTwo.representation k σ ∅ g v) =
      emptyScalarLinearEquiv k f v
    rw [emptyRepresentation_apply])

variable [Fintype F] (hcard : Fintype.card F = 2 ^ f)

include hcard in
/-- Tensor injectivity also survives the empty-support transport. -/
theorem emptyEvaluation_injective : Function.Injective (emptyEvaluation k σ f) := by
  intro v w hvw
  apply BinaryTensorSLTwoEvaluation.evaluation_injective k σ ∅ hcard
  apply (emptyWeightEquiv k σ f).toLinearEquiv.injective
  exact hvw

end Empty
end Kourovka2135.SLTwoFullTensorEvaluation
