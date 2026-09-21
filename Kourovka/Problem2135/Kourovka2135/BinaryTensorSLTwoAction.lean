import Kourovka2135.BinaryTensorSLTwo

/-! Identify the actual tensor SL2 action with the squarefree coefficient action.

The tensor/exterior equivalence is first proved equal to the multilinear
product map. Upper unipotents and split torus matrices are then computed on
actual tensor generators, with no representation classification premise.
-/

set_option autoImplicit false
noncomputable section
universe u v

namespace Kourovka2135.BinaryTensorSLTwo

open BinaryTensorSubsetBasis
open scoped TensorProduct PiTensorProduct IsMulCommutative

variable (k : Type u) [Field k] [CharP k 2] {f : ℕ} (I : Finset (Fin f))

/-- The product of distinct coefficient generators is its exterior basis monomial. -/
theorem prod_coefficient_generator (J : Finset I) :
    (∏ i ∈ J, BinaryTensorCoefficient.generator k I i) =
      BinaryTensorCoefficient.basis k I J := by
  induction J using Finset.induction_on with
  | empty => simp
  | @insert i J hi ih =>
    rw [Finset.prod_insert hi, ih, BinaryTensorCoefficient.generator_mul_basis]
    simp only [hi, ite_false]

/-- The second natural vector gives the unit and the first gives the generator. -/
def localCoefficient (i : I) : (Fin 2 → k) →ₗ[k] BinaryTensorCoefficient.Carrier k I where
  toFun x := x 1 • (1 : BinaryTensorCoefficient.Carrier k I) +
    x 0 • BinaryTensorCoefficient.generator k I i
  map_add' x y := by
    simp only [Pi.add_apply, add_smul]
    abel
  map_smul' a x := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, smul_add, smul_smul]

@[simp] theorem localCoefficient_apply (i : I) (x : Fin 2 → k) :
    localCoefficient k I i x = x 1 • (1 : BinaryTensorCoefficient.Carrier k I) +
      x 0 • BinaryTensorCoefficient.generator k I i := rfl

/-- The concrete multilinear product map from the natural tensor space. -/
def productMap : TensorSpace k I →ₗ[k] BinaryTensorCoefficient.Carrier k I :=
  PiTensorProduct.lift
    ((MultilinearMap.mkPiAlgebra k I (BinaryTensorCoefficient.Carrier k I)).compLinearMap
      (fun i : I => localCoefficient k I i))

@[simp] theorem productMap_tprod (x : I → (Fin 2 → k)) :
    productMap k I (PiTensorProduct.tprod k x) =
      ∏ i : I, localCoefficient k I i (x i) := by
  simp only [productMap, PiTensorProduct.lift.tprod,
    MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply]

theorem localCoefficient_subsetBits (J : Subsets I) (i : I) :
    localCoefficient k I i (Pi.basisFun k (Fin 2) (subsetBits I J i)) =
      if i.val ∈ J.val then BinaryTensorCoefficient.generator k I i else 1 := by
  by_cases hi : i.val ∈ J.val <;> simp [subsetBits, hi, localCoefficient]

@[simp] theorem productMap_tensorBasis (J : Subsets I) :
    productMap k I (tensorBasis k I J) = basis k I J := by
  rw [tensorBasis_apply, productMap_tprod]
  simp only [localCoefficient_subsetBits]
  have hprod : (∏ i : I, if i.val ∈ J.val then
      BinaryTensorCoefficient.generator k I i else 1) =
      ∏ i ∈ (subsetEquiv I).symm J, BinaryTensorCoefficient.generator k I i := by
    simpa only [mem_subsetEquiv_symm_iff] using
      Finset.prod_ite_mem_eq ((subsetEquiv I).symm J)
        (BinaryTensorCoefficient.generator k I)
  rw [hprod, prod_coefficient_generator, basis_apply]

/-- The basis equivalence equals the explicitly constructed product map. -/
theorem tensorEquiv_eq_productMap : (tensorEquiv k I).toLinearMap = productMap k I := by
  apply (tensorBasis k I).ext
  intro J
  simp

/-- Explicit product coordinates for every pure tensor, proved from the actual basis. -/
theorem tensorEquiv_tprod (x : I → (Fin 2 → k)) :
    tensorEquiv k I (PiTensorProduct.tprod k x) =
      ∏ i : I, localCoefficient k I i (x i) := by
  exact (LinearMap.congr_fun (tensorEquiv_eq_productMap k I) _).trans
    (productMap_tprod k I x)

/-- Project the full character onto precisely the included coefficient generators. -/
theorem projection_character (t : k) :
    BinaryTensorCoefficient.projection k I (BinaryExteriorCharacter.character k f t) =
      ∏ i : I, (1 + t ^ (2 ^ i.val.val) • BinaryTensorCoefficient.generator k I i) := by
  let p : Fin f → BinaryTensorCoefficient.Carrier k I := fun i =>
    BinaryTensorCoefficient.projection k I
      (1 + t ^ (2 ^ i.val) • BinaryExteriorAlgebra.generator k f i)
  have hout : ∀ i ∈ (Finset.univ : Finset (Fin f)), i ∉ I → p i = 1 := by
    intro i _ hi
    simp [p, hi]
  calc
    BinaryTensorCoefficient.projection k I (BinaryExteriorCharacter.character k f t) =
        ∏ i : Fin f, p i := by simp only [BinaryExteriorCharacter.character, map_prod, p]
    _ = ∏ i ∈ I, p i := (Finset.prod_subset (Finset.subset_univ I) hout).symm
    _ = ∏ i : I, p i := (Finset.prod_coe_sort I p).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i _
      simp [p, BinaryTensorCoefficient.projection_generator_of_mem k I i i.property]

section Matrices

variable {F : Type v} [Field F] (σ : F →+* k)

/-- A single upper-unipotent tensor factor is multiplication by a square-zero factor. -/
theorem localCoefficient_uni (i : I) (t : F) (x : Fin 2 → k) :
    localCoefficient k I i (naturalTwist k σ i.val.val (SLTwo.uni t) x) =
      (1 + (σ t) ^ (2 ^ i.val.val) • BinaryTensorCoefficient.generator k I i) *
        localCoefficient k I i x := by
  rw [naturalTwist_uni]
  simp [localCoefficient, mul_add, add_smul,
    BinaryTensorCoefficient.generator_square, smul_smul, mul_comm,
    add_assoc, add_comm]

/-- The unipotent character identity on pure tensors. -/
theorem tensorEquiv_uni_tprod (t : F) (x : I → (Fin 2 → k)) :
    tensorEquiv k I (tensorRepresentation k σ I (SLTwo.uni t)
      (PiTensorProduct.tprod k x)) =
      BinaryExteriorCharacter.character k f (σ t) •
        tensorEquiv k I (PiTensorProduct.tprod k x) := by
  rw [tensorRepresentation_tprod, tensorEquiv_tprod]
  simp only [localCoefficient_uni, Finset.prod_mul_distrib]
  rw [BinaryTensorCoefficient.smul_eq, projection_character, tensorEquiv_tprod]

/-- The actual SL2 representation restricts to the previously constructed additive action. -/
theorem representation_uni (t : F) (v : BinaryTensorCoefficient.Carrier k I) :
    representation k σ I (SLTwo.uni t) v =
      BinaryExteriorCharacter.character k f (σ t) • v := by
  have h : (tensorEquiv k I).toLinearMap.comp
      (tensorRepresentation k σ I (SLTwo.uni t)) =
      (LinearMap.mulLeft k (BinaryTensorCoefficient.projection k I
        (BinaryExteriorCharacter.character k f (σ t)))).comp
          (tensorEquiv k I).toLinearMap := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro x
    exact tensorEquiv_uni_tprod k I σ t x
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.mulLeft_apply,
    representation_apply, LinearEquiv.apply_symm_apply, BinaryTensorCoefficient.smul_eq] using
      LinearMap.congr_fun h ((tensorEquiv k I).symm v)

/-- The embedded torus parameter remains a unit. -/
def mappedUnit (r : Fˣ) : kˣ := Units.map σ.toMonoidHom r

omit [CharP k 2] in
@[simp] theorem mappedUnit_val (r : Fˣ) : (mappedUnit k σ r : k) = σ (r : F) := rfl

/-- The natural weight is positive exactly at present subset indices. -/
def localTorusWeight (r : kˣ) (J : Subsets I) (i : I) : kˣ :=
  if i.val ∈ J.val then r ^ (2 ^ i.val.val) else (r ^ (2 ^ i.val.val))⁻¹

theorem naturalTwist_tor_subsetBits (r : Fˣ) (J : Subsets I) (i : I) :
    naturalTwist k σ i.val.val (SLTwo.tor r)
      (Pi.basisFun k (Fin 2) (subsetBits I J i)) =
      (localTorusWeight k I (mappedUnit k σ r) J i : k) •
        Pi.basisFun k (Fin 2) (subsetBits I J i) := by
  rw [naturalTwist_tor]
  funext j
  by_cases hi : i.val ∈ J.val
  · fin_cases j <;> simp [subsetBits, hi, localTorusWeight, mappedUnit]
  · fin_cases j <;> simp [subsetBits, hi, localTorusWeight, mappedUnit]

omit [CharP k 2] in
/-- Multiply the positive and negative natural weights without truncated subtraction. -/
theorem prod_localTorusWeight (r : kˣ) (J : Subsets I) :
    (∏ i : I, localTorusWeight k I r J i) =
      r ^ (2 * BinaryTensorTorus.binaryWeight J.val) /
        r ^ BinaryTensorTorus.binaryWeight I := by
  have hlocal (i : I) : localTorusWeight k I r J i =
      (r ^ (2 ^ i.val.val))⁻¹ *
        (if i.val ∈ J.val then r ^ (2 * (2 ^ i.val.val)) else 1) := by
    by_cases hi : i.val ∈ J.val
    · have hp : r ^ (2 * (2 ^ i.val.val)) = (r ^ (2 ^ i.val.val)) ^ 2 := by
        rw [Nat.mul_comm 2, pow_mul]
      simp [localTorusWeight, hi, hp, pow_two]
    · simp [localTorusWeight, hi]
  have hfull : (∏ i : I, r ^ (2 ^ i.val.val)) =
      r ^ BinaryTensorTorus.binaryWeight I := by
    rw [Finset.prod_coe_sort I (fun i : Fin f => r ^ (2 ^ i.val)),
      Finset.prod_pow_eq_pow_sum]
    rfl
  have hpart : (∏ i : I, if i.val ∈ J.val then
      r ^ (2 * (2 ^ i.val.val)) else 1) =
      r ^ (2 * BinaryTensorTorus.binaryWeight J.val) := by
    let p : Fin f → kˣ := fun i => if i ∈ J.val then r ^ (2 * (2 ^ i.val)) else 1
    have hsub : (∏ i ∈ J.val, p i) = ∏ i ∈ I, p i :=
      Finset.prod_subset J.property (by intro i _ hi; simp [p, hi])
    calc
      (∏ i : I, if i.val ∈ J.val then r ^ (2 * (2 ^ i.val.val)) else 1) =
          ∏ i ∈ I, p i := Finset.prod_coe_sort I p
      _ = ∏ i ∈ J.val, p i := hsub.symm
      _ = ∏ i ∈ J.val, r ^ (2 * (2 ^ i.val)) := by
        apply Finset.prod_congr rfl
        intro i hi
        simp only [p, hi, ite_true]
      _ = r ^ (2 * BinaryTensorTorus.binaryWeight J.val) := by
        rw [Finset.prod_pow_eq_pow_sum, ← Finset.mul_sum]
        rfl
  simp only [hlocal, Finset.prod_mul_distrib, Finset.prod_inv_distrib, hfull, hpart,
    div_eq_mul_inv]
  exact mul_comm _ _

/-- Actual torus basis weights for the tensor product, transferred to the coefficient space. -/
theorem representation_tor_basis (r : Fˣ) (J : Subsets I) :
    representation k σ I (SLTwo.tor r) (basis k I J) =
      (((mappedUnit k σ r) ^ (2 * BinaryTensorTorus.binaryWeight J.val) /
        (mappedUnit k σ r) ^ BinaryTensorTorus.binaryWeight I : kˣ) : k) • basis k I J := by
  rw [representation_apply, tensorEquiv_symm_basis, tensorBasis_apply,
    tensorRepresentation_tprod]
  simp only [naturalTwist_tor_subsetBits]
  rw [(PiTensorProduct.tprod k).map_smul_univ, map_smul]
  rw [← tensorBasis_apply, tensorEquiv_basis]
  congr 1
  rw [← Units.coe_prod]
  exact congrArg (fun z : kˣ => (z : k)) (prod_localTorusWeight k I (mappedUnit k σ r) J)

/-- The actual natural tensor torus action is precisely the existing coefficient torus action. -/
theorem representation_tor (r : Fˣ) :
    representation k σ I (SLTwo.tor r) =
      (BinaryTensorTorus.torus k I (mappedUnit k σ r)).toLinearMap := by
  apply (basis k I).ext
  intro J
  rw [representation_tor_basis, LinearEquiv.coe_coe, BinaryTensorTorus.torus_basis]

end Matrices

end Kourovka2135.BinaryTensorSLTwo
