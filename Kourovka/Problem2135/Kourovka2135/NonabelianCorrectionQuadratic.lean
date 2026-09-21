import Kourovka2135.NonabelianCorrectionProduct
import Kourovka2135.NonabelianCorrectionLinear
import Kourovka2135.CommutatorBilinearMap
import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-! The actual central correction on the kernel of its linear projection,
and its normalization on every affine fiber, as binary quadratic maps. -/
set_option autoImplicit false
namespace Kourovka2135
open scoped IsMulCommutative
variable {N : Type*} [Group N]
variable [IsElementaryAbelian 2 (N ⧸ Subgroup.center N)]
variable [IsElementaryAbelian 2 (commutator N)]
variable [IsElementaryAbelian 2 (Subgroup.center N)]

abbrev CorrectionSpace (N : Type*) [Group N] :=
  Additive (N ⧸ Subgroup.center N) × Additive (N ⧸ Subgroup.center N)

def quotientCorrection (D E : MulAut N)
    (hD : ∀ z ∈ Subgroup.center N, D z = z)
    (hE : ∀ z ∈ Subgroup.center N, E z = z) (a : CorrectionSpace N) : N :=
  centerQuotientCorrection D E hD hE a.1.toMul a.2.toMul

theorem quotientCorrection_zero (D E : MulAut N)
    (hD : ∀ z ∈ Subgroup.center N, D z = z)
    (hE : ∀ z ∈ Subgroup.center N, E z = z) :
    quotientCorrection D E hD hE 0 = 1 := by
  change automorphismCorrection D E 1 1 = 1
  simp only [automorphismCorrection, map_one, inv_one, mul_one]

theorem quotientCorrection_mem_center (D E : MulAut N)
    (hD : ∀ z ∈ Subgroup.center N, D z = z)
    (hE : ∀ z ∈ Subgroup.center N, E z = z)
    {a : CorrectionSpace N} (ha : a ∈ (correctionLinearMap 2 D E).ker) :
    quotientCorrection D E hD hE a ∈ Subgroup.center N := by
  apply (QuotientGroup.eq_one_iff _).mp
  have hh := quotient_centerQuotientCorrection 2 D E hD hE a.1 a.2
  change Additive.ofMul (QuotientGroup.mk' (Subgroup.center N)
    (quotientCorrection D E hD hE a)) = correctionLinearMap 2 D E a at hh
  rw [show correctionLinearMap 2 D E a = 0 from ha] at hh
  exact hh

def centerCommutatorBilinear (hC : commutator N ≤ Subgroup.center N) :
    Additive (N ⧸ Subgroup.center N) →ₗ[ZMod 2]
      Additive (N ⧸ Subgroup.center N) →ₗ[ZMod 2] Additive (Subgroup.center N) :=
  (centralCommutatorBilinearMap hC 2).compr₂
    ((Subgroup.inclusion hC).toAdditive.toZModLinearMap 2)

def correctionBilinear (hC : commutator N ≤ Subgroup.center N) (D E : MulAut N) :
    CorrectionSpace N →ₗ[ZMod 2]
      CorrectionSpace N →ₗ[ZMod 2] Additive (Subgroup.center N) :=
  (centerCommutatorBilinear hC).compl₁₂ (LinearMap.fst _ _ _)
      ((centerActionLinear 2 D).comp (LinearMap.snd _ _ _)) +
    ((centerCommutatorBilinear hC).compl₁₂
      ((centerActionLinear 2 E).comp (LinearMap.fst _ _ _))
      (LinearMap.snd _ _ _)).flip

theorem quotientCorrection_add_of_mem_ker
    (hC : commutator N ≤ Subgroup.center N) (D E : MulAut N)
    (hD : ∀ z ∈ Subgroup.center N, D z = z)
    (hE : ∀ z ∈ Subgroup.center N, E z = z)
    (a b : CorrectionSpace N) (ha : a ∈ (correctionLinearMap 2 D E).ker) :
    quotientCorrection D E hD hE (a + b) =
      quotientCorrection D E hD hE a * quotientCorrection D E hD hE b *
        ((correctionBilinear hC D E a b).toMul : N) := by
  have hc := quotientCorrection_mem_center D E hD hE ha
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

def centralCorrection (D E : MulAut N)
    (hD : ∀ z ∈ Subgroup.center N, D z = z)
    (hE : ∀ z ∈ Subgroup.center N, E z = z)
    (a : (correctionLinearMap 2 D E).ker) : Additive (Subgroup.center N) :=
  Additive.ofMul ⟨quotientCorrection D E hD hE a,
    quotientCorrection_mem_center D E hD hE a.property⟩

theorem centralCorrection_zero (D E : MulAut N)
    (hD : ∀ z ∈ Subgroup.center N, D z = z)
    (hE : ∀ z ∈ Subgroup.center N, E z = z) :
    centralCorrection D E hD hE 0 = 0 := by
  apply Subtype.ext
  exact quotientCorrection_zero D E hD hE

theorem centralCorrection_add (hC : commutator N ≤ Subgroup.center N)
    (D E : MulAut N)
    (hD : ∀ z ∈ Subgroup.center N, D z = z)
    (hE : ∀ z ∈ Subgroup.center N, E z = z)
    (a b : (correctionLinearMap 2 D E).ker) :
    centralCorrection D E hD hE (a + b) =
      centralCorrection D E hD hE a + centralCorrection D E hD hE b +
        correctionBilinear hC D E a b := by
  apply Subtype.ext
  exact quotientCorrection_add_of_mem_ker hC D E hD hE a b a.property

def centralCorrectionQuadratic (hC : commutator N ≤ Subgroup.center N)
    (D E : MulAut N)
    (hD : ∀ z ∈ Subgroup.center N, D z = z)
    (hE : ∀ z ∈ Subgroup.center N, E z = z) :
    QuadraticMap (ZMod 2) (correctionLinearMap 2 D E).ker
      (Additive (Subgroup.center N)) where
  toFun := centralCorrection D E hD hE
  toFun_smul r a := by
    have hr : r = 0 ∨ r = 1 := by
      fin_cases r
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases hr with rfl | rfl
    · simpa only [zero_smul, zero_mul] using centralCorrection_zero D E hD hE
    · simp only [one_smul, one_mul]
  exists_companion' := ⟨(correctionBilinear hC D E).compl₁₂
    (correctionLinearMap 2 D E).ker.subtype (correctionLinearMap 2 D E).ker.subtype,
    centralCorrection_add hC D E hD hE⟩

theorem centralCorrectionQuadratic_polar (hC : commutator N ≤ Subgroup.center N)
    (D E : MulAut N)
    (hD : ∀ z ∈ Subgroup.center N, D z = z)
    (hE : ∀ z ∈ Subgroup.center N, E z = z)
    (a b : (correctionLinearMap 2 D E).ker) :
    (centralCorrectionQuadratic hC D E hD hE).polarBilin a b =
      correctionBilinear hC D E a b := by
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar]
  change centralCorrection D E hD hE (a + b) - centralCorrection D E hD hE a -
    centralCorrection D E hD hE b = _
  rw [centralCorrection_add hC]
  abel

end Kourovka2135
