import Kourovka2135.BinaryTensorSLTwoSimplicity
import Kourovka2135.SLTwoHomogeneousFunctions

/-! Actual evaluation of binary Frobenius tensors as homogeneous functions.

The map is constructed by the universal property of the tensor product,
with each natural factor evaluated at the corresponding Frobenius power
of the point. Scaling and the full SL2 action are checked on pure tensors.
The top tensor evaluates to one on every affine chart representative, so
simplicity makes this genuine intertwining map injective.
-/

set_option autoImplicit false
noncomputable section
universe u v

namespace Kourovka2135.BinaryTensorSLTwoEvaluation

open BinaryTensorSLTwo BinaryTensorSubsetBasis
open scoped TensorProduct PiTensorProduct

variable (k : Type u) [Field k] {F : Type v} [Field F] (σ : F →+* k)
variable {f : ℕ} (I : Finset (Fin f))

/-- The binary subset weight is the sum over the actual tensor factors. -/
theorem subsetWeight_eq_sum :
    BinaryExteriorGroupAlgebra.subsetWeight f I = ∑ i : I, 2 ^ i.val.val := by
  exact (Finset.sum_coe_sort I (fun i : Fin f => 2 ^ i.val)).symm

/-- Evaluation of one natural Frobenius factor at a nonzero vector. -/
def localEvaluation (n : ℕ) (z : SLTwoHomogeneousFunctions.Point F) :
    (Fin 2 → k) →ₗ[k] k where
  toFun x := x 0 * σ (z.val 0) ^ (2 ^ n) + x 1 * σ (z.val 1) ^ (2 ^ n)
  map_add' x y := by
    simp only [Pi.add_apply]
    ring
  map_smul' a x := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

@[simp] theorem localEvaluation_apply (n : ℕ) (z : SLTwoHomogeneousFunctions.Point F)
    (x : Fin 2 → k) :
    localEvaluation k σ n z x =
      x 0 * σ (z.val 0) ^ (2 ^ n) + x 1 * σ (z.val 1) ^ (2 ^ n) := rfl

/-- Scaling has the exact Frobenius weight on each factor. -/
theorem localEvaluation_scale (n : ℕ) (a : Fˣ)
    (z : SLTwoHomogeneousFunctions.Point F) (x : Fin 2 → k) :
    localEvaluation k σ n (SLTwoHomogeneousFunctions.scalePoint a z) x =
      σ (a : F) ^ (2 ^ n) * localEvaluation k σ n z x := by
  simp only [localEvaluation_apply, SLTwoHomogeneousFunctions.scalePoint_apply,
    map_mul, mul_pow]
  ring

/-- Tensor evaluation at an actual point, constructed from a multilinear product. -/
def atPoint (z : SLTwoHomogeneousFunctions.Point F) : TensorSpace k I →ₗ[k] k :=
  PiTensorProduct.lift
    ((MultilinearMap.mkPiAlgebra k I k).compLinearMap
      (fun i : I => localEvaluation k σ i.val.val z))

@[simp] theorem atPoint_tprod (z : SLTwoHomogeneousFunctions.Point F)
    (x : I → (Fin 2 → k)) :
    atPoint k σ I z (PiTensorProduct.tprod k x) =
      ∏ i : I, localEvaluation k σ i.val.val z (x i) := by
  simp only [atPoint, PiTensorProduct.lift.tprod,
    MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply]

/-- The complete tensor scales by the sum of its binary weights. -/
theorem atPoint_scale (a : Fˣ) (z : SLTwoHomogeneousFunctions.Point F) :
    atPoint k σ I (SLTwoHomogeneousFunctions.scalePoint a z) =
      σ (a : F) ^ (BinaryExteriorGroupAlgebra.subsetWeight f I) • atPoint k σ I z := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  change atPoint k σ I (SLTwoHomogeneousFunctions.scalePoint a z)
      (PiTensorProduct.tprod k x) =
    σ (a : F) ^ (BinaryExteriorGroupAlgebra.subsetWeight f I) *
      atPoint k σ I z (PiTensorProduct.tprod k x)
  simp only [atPoint_tprod, localEvaluation_scale, Finset.prod_mul_distrib]
  rw [Finset.prod_pow_eq_pow_sum, ← subsetWeight_eq_sum I]

/-- The pointwise tensor evaluation lands in the actual homogeneous-function subspace. -/
def tensorEvaluation : TensorSpace k I →ₗ[k]
    SLTwoHomogeneousFunctions.Carrier k σ (BinaryExteriorGroupAlgebra.subsetWeight f I) :=
  (LinearMap.pi (fun z : SLTwoHomogeneousFunctions.Point F => atPoint k σ I z)).codRestrict
    (SLTwoHomogeneousFunctions.space k σ (BinaryExteriorGroupAlgebra.subsetWeight f I))
    (fun v a z => LinearMap.congr_fun (atPoint_scale k σ I a z) v)

@[simp] theorem tensorEvaluation_apply (v : TensorSpace k I)
    (z : SLTwoHomogeneousFunctions.Point F) :
    tensorEvaluation k σ I v z = atPoint k σ I z v := rfl

/-- The pure-tensor formula is proved for the actual tensor evaluation map. -/
theorem tensorEvaluation_tprod (x : I → (Fin 2 → k))
    (z : SLTwoHomogeneousFunctions.Point F) :
    tensorEvaluation k σ I (PiTensorProduct.tprod k x) z =
      ∏ i : I, ((x i) 0 * σ (z.val 0) ^ (2 ^ i.val.val) +
        (x i) 1 * σ (z.val 1) ^ (2 ^ i.val.val)) := by
  simp only [tensorEvaluation_apply, atPoint_tprod, localEvaluation_apply]

/-- Evaluation on the existing coefficient carrier through the proved tensor equivalence. -/
def evaluationLinear : BinaryTensorCoefficient.Carrier k I →ₗ[k]
    SLTwoHomogeneousFunctions.Carrier k σ (BinaryExteriorGroupAlgebra.subsetWeight f I) :=
  (tensorEvaluation k σ I).comp (tensorEquiv k I).symm.toLinearMap

@[simp] theorem evaluationLinear_apply (v : BinaryTensorCoefficient.Carrier k I)
    (z : SLTwoHomogeneousFunctions.Point F) :
    evaluationLinear k σ I v z = atPoint k σ I z ((tensorEquiv k I).symm v) := rfl

/-- A subset basis factor selects the matching point coordinate. -/
theorem localEvaluation_subsetBits (J : Subsets I) (i : I)
    (z : SLTwoHomogeneousFunctions.Point F) :
    localEvaluation k σ i.val.val z (Pi.basisFun k (Fin 2) (subsetBits I J i)) =
      if i.val ∈ J.val then σ (z.val 0) ^ (2 ^ i.val.val)
      else σ (z.val 1) ^ (2 ^ i.val.val) := by
  by_cases hi : i.val ∈ J.val <;> simp [localEvaluation, subsetBits, hi]

/-- Evaluation of every actual coefficient basis vector. -/
theorem evaluationLinear_basis (J : Subsets I) (z : SLTwoHomogeneousFunctions.Point F) :
    evaluationLinear k σ I (basis k I J) z =
      ∏ i : I, if i.val ∈ J.val then σ (z.val 0) ^ (2 ^ i.val.val)
        else σ (z.val 1) ^ (2 ^ i.val.val) := by
  rw [evaluationLinear_apply, tensorEquiv_symm_basis, tensorBasis_apply, atPoint_tprod]
  exact Finset.prod_congr rfl (fun i _ => localEvaluation_subsetBits k σ I J i z)

/-- The top tensor evaluates to the first coordinate to the full subset weight. -/
theorem evaluationLinear_top (z : SLTwoHomogeneousFunctions.Point F) :
    evaluationLinear k σ I (basis k I (topIndex I)) z =
      σ (z.val 0) ^ (BinaryExteriorGroupAlgebra.subsetWeight f I) := by
  rw [evaluationLinear_basis]
  calc
    (∏ i : I, if i.val ∈ (topIndex I).val then σ (z.val 0) ^ (2 ^ i.val.val)
        else σ (z.val 1) ^ (2 ^ i.val.val)) =
        ∏ i : I, σ (z.val 0) ^ (2 ^ i.val.val) := by
      apply Finset.prod_congr rfl
      intro i _
      simp only [topIndex, i.property, ite_true]
    _ = _ := by rw [Finset.prod_pow_eq_pow_sum, ← subsetWeight_eq_sum I]

@[simp] theorem evaluationLinear_top_affine (t : F) :
    evaluationLinear k σ I (basis k I (topIndex I)) (SLTwoHomogeneousFunctions.affine t) = 1 := by
  rw [evaluationLinear_top]
  simp

/-- Positive homogeneous weight gives zero at infinity. -/
theorem evaluationLinear_top_infinity
    (hn : 0 < BinaryExteriorGroupAlgebra.subsetWeight f I) :
    evaluationLinear k σ I (basis k I (topIndex I)) (SLTwoHomogeneousFunctions.infinity F) = 0 := by
  rw [evaluationLinear_top]
  simp [Nat.ne_of_gt hn]

/-- For positive weight the top vector is precisely the affine-constant, infinity-zero vector. -/
theorem evaluationLinear_top_coordinates
    (hn : 0 < BinaryExteriorGroupAlgebra.subsetWeight f I) :
    SLTwoHomogeneousFunctions.coordinates k σ (BinaryExteriorGroupAlgebra.subsetWeight f I)
      (evaluationLinear k σ I (basis k I (topIndex I))) = (0, fun _ : F => 1) := by
  apply Prod.ext
  · exact evaluationLinear_top_infinity k σ I hn
  · funext t
    exact evaluationLinear_top_affine k σ I t

section Action

variable [CharP k 2]

/-- The natural Frobenius action is adjoint to the genuine transpose action on points. -/
theorem localEvaluation_action (n : ℕ) (g : SLTwo.SL2 F)
    (z : SLTwoHomogeneousFunctions.Point F) (x : Fin 2 → k) :
    localEvaluation k σ n z (naturalTwist k σ n g x) =
      localEvaluation k σ n (SLTwoHomogeneousFunctions.pointAction g z) x := by
  have hcoord (j : Fin 2) :
      σ ((SLTwoHomogeneousFunctions.pointAction g z).val j) ^ (2 ^ n) =
        σ (z.val 0) ^ (2 ^ n) * σ (g.val 0 j) ^ (2 ^ n) +
        σ (z.val 1) ^ (2 ^ n) * σ (g.val 1 j) ^ (2 ^ n) := by
    change twistEmbedding k σ n ((SLTwoHomogeneousFunctions.pointAction g z).val j) = _
    rw [SLTwoHomogeneousFunctions.pointAction_val]
    simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_two,
      map_add, map_mul, twistEmbedding_apply]
  simp only [localEvaluation_apply, naturalTwist_apply, Fin.sum_univ_two, hcoord]
  ring

/-- Full SL2 equivariance on the underlying tensor space. -/
theorem atPoint_action (g : SLTwo.SL2 F) (z : SLTwoHomogeneousFunctions.Point F) :
    (atPoint k σ I z).comp (tensorRepresentation k σ I g) =
      atPoint k σ I (SLTwoHomogeneousFunctions.pointAction g z) := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  change atPoint k σ I z (tensorRepresentation k σ I g (PiTensorProduct.tprod k x)) =
    atPoint k σ I (SLTwoHomogeneousFunctions.pointAction g z) (PiTensorProduct.tprod k x)
  rw [tensorRepresentation_tprod, atPoint_tprod, atPoint_tprod]
  exact Finset.prod_congr rfl (fun i _ => localEvaluation_action k σ i.val.val g z (x i))

/-- Equivariance is proved before transporting to the coefficient carrier. -/
theorem tensorEvaluation_action (g : SLTwo.SL2 F) (v : TensorSpace k I) :
    tensorEvaluation k σ I (tensorRepresentation k σ I g v) =
      SLTwoHomogeneousFunctions.representation k σ
        (BinaryExteriorGroupAlgebra.subsetWeight f I) g (tensorEvaluation k σ I v) := by
  apply Subtype.ext
  funext z
  exact LinearMap.congr_fun (atPoint_action k σ I g z) v

/-- The coefficient-space evaluation intertwines the full concrete SL2 representation. -/
theorem evaluationLinear_action (g : SLTwo.SL2 F) (v : BinaryTensorCoefficient.Carrier k I) :
    evaluationLinear k σ I (representation k σ I g v) =
      SLTwoHomogeneousFunctions.representation k σ
        (BinaryExteriorGroupAlgebra.subsetWeight f I) g (evaluationLinear k σ I v) := by
  change tensorEvaluation k σ I ((tensorEquiv k I).symm (representation k σ I g v)) = _
  rw [representation_apply, LinearEquiv.symm_apply_apply]
  exact tensorEvaluation_action k σ I g ((tensorEquiv k I).symm v)

/-- The actual tensor-to-functions intertwining map, with no identification premise. -/
def evaluation : Representation.IntertwiningMap (representation k σ I)
    (SLTwoHomogeneousFunctions.representation k σ
      (BinaryExteriorGroupAlgebra.subsetWeight f I)) :=
  (evaluationLinear k σ I).intertwiningMap_of_isIntertwiningMap
    (representation k σ I)
    (SLTwoHomogeneousFunctions.representation k σ (BinaryExteriorGroupAlgebra.subsetWeight f I))
    (evaluationLinear_action k σ I)

@[simp] theorem evaluation_apply (v : BinaryTensorCoefficient.Carrier k I) :
    evaluation k σ I v = evaluationLinear k σ I v := rfl

/-- The map is nonzero because the top vector has affine value one, also for empty support. -/
theorem evaluation_ne_zero : evaluation k σ I ≠ 0 := by
  intro h
  have hz : evaluation k σ I (basis k I (topIndex I))
      (SLTwoHomogeneousFunctions.affine (0 : F)) = 0 := by
    rw [h]
    rfl
  rw [evaluation_apply, evaluationLinear_top_affine] at hz
  exact one_ne_zero hz

variable [Fintype F] (hcard : Fintype.card F = 2 ^ f)

include hcard

/-- Simplicity proves injectivity over every characteristic-two field containing F. -/
theorem evaluation_injective : Function.Injective (evaluation k σ I) := by
  let : (representation k σ I).IsIrreducible :=
    BinaryTensorSLTwoSimplicity.isIrreducible k I σ hcard
  exact (Representation.IsIrreducible.injective_or_eq_zero (evaluation k σ I)).resolve_right
    (evaluation_ne_zero k σ I)

end Action
end Kourovka2135.BinaryTensorSLTwoEvaluation
