import Kourovka2135.DerivedCorrectionLinear

/-! Quadratic corrections valued in N' on every affine fiber modulo N'.
The center is allowed to have elements of order four. -/
set_option autoImplicit false
namespace Kourovka2135
open scoped IsMulCommutative
variable {N : Type*} [Group N]
variable [IsElementaryAbelian 2 (N ⧸ Subgroup.center N)]
variable [IsElementaryAbelian 2 (N ⧸ commutator N)]
variable [IsElementaryAbelian 2 (commutator N)]

def derivedCorrectionBilinear (hC : commutator N ≤ Subgroup.center N) (D E : MulAut N) :
    CorrectionSpace N →ₗ[ZMod 2]
      CorrectionSpace N →ₗ[ZMod 2] Additive (commutator N) :=
  (centralCommutatorBilinearMap hC 2).compl₁₂ (LinearMap.fst _ _ _)
      ((centerActionLinear 2 D).comp (LinearMap.snd _ _ _)) +
    ((centralCommutatorBilinearMap hC 2).compl₁₂
      ((centerActionLinear 2 E).comp (LinearMap.fst _ _ _))
      (LinearMap.snd _ _ _)).flip

theorem quotientCorrection_add_of_derived_kernel
    (hC : commutator N ≤ Subgroup.center N) (D E : MulAut N)
    (hD : ∀ z ∈ Subgroup.center N, D z = z)
    (hE : ∀ z ∈ Subgroup.center N, E z = z)
    (a b : CorrectionSpace N) (ha : a ∈ (derivedCorrectionLinear hC D E hD hE).ker) :
    quotientCorrection D E hD hE (a + b) =
      quotientCorrection D E hD hE a * quotientCorrection D E hD hE b *
        ((derivedCorrectionBilinear hC D E a b).toMul : N) := by
  have hc := hC ((derivedCorrectionLinear_mem_ker_iff hC D E hD hE a).mp ha)
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (Subgroup.center N) a.1.toMul
  obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective (Subgroup.center N) a.2.toMul
  obtain ⟨x', hx'⟩ := QuotientGroup.mk'_surjective (Subgroup.center N) b.1.toMul
  obtain ⟨y', hy'⟩ := QuotientGroup.mk'_surjective (Subgroup.center N) b.2.toMul
  have ha' : a = (Additive.ofMul (QuotientGroup.mk' (Subgroup.center N) x),
      Additive.ofMul (QuotientGroup.mk' (Subgroup.center N) y)) := Prod.ext hx.symm hy.symm
  have hb' : b = (Additive.ofMul (QuotientGroup.mk' (Subgroup.center N) x'),
      Additive.ofMul (QuotientGroup.mk' (Subgroup.center N) y')) := Prod.ext hx'.symm hy'.symm
  rw [ha', hb']
  rw [ha'] at hc
  change automorphismCorrection D E (x * x') (y * y') =
    automorphismCorrection D E x y * automorphismCorrection D E x' y' *
      (paperCommutator x (D y') * paperCommutator (E x') y)
  exact automorphismCorrection_mul_of_central_value hC D E x y x' y' hc

def derivedCentralCorrection (hC : commutator N ≤ Subgroup.center N) (D E : MulAut N)
    (hD : ∀ z ∈ Subgroup.center N, D z = z)
    (hE : ∀ z ∈ Subgroup.center N, E z = z)
    (a : (derivedCorrectionLinear hC D E hD hE).ker) : Additive (commutator N) :=
  Additive.ofMul ⟨quotientCorrection D E hD hE a,
    (derivedCorrectionLinear_mem_ker_iff hC D E hD hE a).mp a.property⟩

theorem derivedCentralCorrection_zero
    (hC : commutator N ≤ Subgroup.center N) (D E : MulAut N)
    (hD : ∀ z ∈ Subgroup.center N, D z = z)
    (hE : ∀ z ∈ Subgroup.center N, E z = z) :
    derivedCentralCorrection hC D E hD hE 0 = 0 := by
  apply Subtype.ext
  change automorphismCorrection D E 1 1 = 1
  simp only [automorphismCorrection, map_one, inv_one, mul_one]

theorem derivedCentralCorrection_add (hC : commutator N ≤ Subgroup.center N)
    (D E : MulAut N)
    (hD : ∀ z ∈ Subgroup.center N, D z = z)
    (hE : ∀ z ∈ Subgroup.center N, E z = z)
    (a b : (derivedCorrectionLinear hC D E hD hE).ker) :
    derivedCentralCorrection hC D E hD hE (a + b) =
      derivedCentralCorrection hC D E hD hE a + derivedCentralCorrection hC D E hD hE b +
        derivedCorrectionBilinear hC D E a b := by
  apply Subtype.ext
  exact quotientCorrection_add_of_derived_kernel hC D E hD hE a b a.property

def derivedAffineCorrectionQuadratic (hC : commutator N ≤ Subgroup.center N)
    (D E : MulAut N)
    (hD : ∀ z ∈ Subgroup.center N, D z = z)
    (hE : ∀ z ∈ Subgroup.center N, E z = z) (b : CorrectionSpace N) :
    QuadraticMap (ZMod 2) (derivedCorrectionLinear hC D E hD hE).ker
      (Additive (commutator N)) where
  toFun a := derivedCentralCorrection hC D E hD hE a + derivedCorrectionBilinear hC D E a b
  toFun_smul r a := by
    have hr : r = 0 ∨ r = 1 := by
      fin_cases r
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases hr with rfl | rfl
    · simp only [zero_smul, zero_mul, Submodule.coe_zero,
        derivedCentralCorrection_zero, map_zero, LinearMap.zero_apply, add_zero]
    · simp only [one_smul, one_mul]
  exists_companion' := by
    refine ⟨(derivedCorrectionBilinear hC D E).compl₁₂
      (derivedCorrectionLinear hC D E hD hE).ker.subtype
      (derivedCorrectionLinear hC D E hD hE).ker.subtype, ?_⟩
    intro a a'
    change derivedCentralCorrection hC D E hD hE (a + a') +
      derivedCorrectionBilinear hC D E ((a : CorrectionSpace N) + a') b = _
    rw [derivedCentralCorrection_add hC, map_add, LinearMap.add_apply]
    change _ =
      (derivedCentralCorrection hC D E hD hE a + derivedCorrectionBilinear hC D E a b) +
      (derivedCentralCorrection hC D E hD hE a' + derivedCorrectionBilinear hC D E a' b) +
      derivedCorrectionBilinear hC D E a a'
    abel

theorem derivedAffineCorrectionQuadratic_polar (hC : commutator N ≤ Subgroup.center N)
    (D E : MulAut N)
    (hD : ∀ z ∈ Subgroup.center N, D z = z)
    (hE : ∀ z ∈ Subgroup.center N, E z = z) (b : CorrectionSpace N)
    (a a' : (derivedCorrectionLinear hC D E hD hE).ker) :
    (derivedAffineCorrectionQuadratic hC D E hD hE b).polarBilin a a' =
      derivedCorrectionBilinear hC D E a a' := by
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar]
  change (derivedCentralCorrection hC D E hD hE (a + a') +
      derivedCorrectionBilinear hC D E ((a : CorrectionSpace N) + a') b) -
    (derivedCentralCorrection hC D E hD hE a + derivedCorrectionBilinear hC D E a b) -
    (derivedCentralCorrection hC D E hD hE a' + derivedCorrectionBilinear hC D E a' b) = _
  rw [derivedCentralCorrection_add hC, map_add, LinearMap.add_apply]
  abel

theorem quotientCorrection_add_eq_derivedAffine (hC : commutator N ≤ Subgroup.center N)
    (D E : MulAut N)
    (hD : ∀ z ∈ Subgroup.center N, D z = z)
    (hE : ∀ z ∈ Subgroup.center N, E z = z) (b : CorrectionSpace N)
    (a : (derivedCorrectionLinear hC D E hD hE).ker) :
    quotientCorrection D E hD hE (b + a) = quotientCorrection D E hD hE b *
      (((derivedAffineCorrectionQuadratic hC D E hD hE b) a).toMul : N) := by
  rw [add_comm b, quotientCorrection_add_of_derived_kernel hC D E hD hE _ _ a.property]
  change quotientCorrection D E hD hE a * quotientCorrection D E hD hE b *
      ((derivedCorrectionBilinear hC D E a b).toMul : N) =
    quotientCorrection D E hD hE b *
      (quotientCorrection D E hD hE a * ((derivedCorrectionBilinear hC D E a b).toMul : N))
  rw [← mul_assoc]
  exact congrArg (fun z : N => z * ((derivedCorrectionBilinear hC D E a b).toMul : N))
    (Subgroup.mem_center_iff.mp
      (hC ((derivedCorrectionLinear_mem_ker_iff hC D E hD hE a).mp a.property)) _).symm

end Kourovka2135
