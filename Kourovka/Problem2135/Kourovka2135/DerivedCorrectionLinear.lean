import Kourovka2135.NonabelianCorrectionQuadratic

/-! The actual correction modulo the derived subgroup, without assuming
that the center has exponent two or equals the derived subgroup. -/
set_option autoImplicit false
namespace Kourovka2135
open scoped IsMulCommutative
variable {N : Type*} [Group N]
variable [IsElementaryAbelian 2 (N ⧸ Subgroup.center N)]
variable [IsElementaryAbelian 2 (N ⧸ commutator N)]

theorem quotient_commutator_paperCommutator (x y : N) :
    QuotientGroup.mk' (commutator N) (paperCommutator x y) = 1 :=
  (QuotientGroup.eq_one_iff _).mpr (paperCommutator_mem_commutator x y)

def derivedCorrectionLinear (hC : commutator N ≤ Subgroup.center N) (D E : MulAut N)
    (hD : ∀ z ∈ Subgroup.center N, D z = z)
    (hE : ∀ z ∈ Subgroup.center N, E z = z) :
    CorrectionSpace N →ₗ[ZMod 2] Additive (N ⧸ commutator N) :=
  AddMonoidHom.toZModLinearMap 2 {
    toFun a := Additive.ofMul
      (QuotientGroup.mk' (commutator N) (quotientCorrection D E hD hE a))
    map_zero' := by
      change Additive.ofMul (QuotientGroup.mk' (commutator N)
        (automorphismCorrection D E 1 1)) = 0
      simp only [automorphismCorrection, map_one, inv_one, mul_one, ofMul_one]
    map_add' := by
      intro a b
      obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (Subgroup.center N) a.1.toMul
      obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective (Subgroup.center N) a.2.toMul
      obtain ⟨x', hx'⟩ := QuotientGroup.mk'_surjective (Subgroup.center N) b.1.toMul
      obtain ⟨y', hy'⟩ := QuotientGroup.mk'_surjective (Subgroup.center N) b.2.toMul
      have ha : a = (Additive.ofMul (QuotientGroup.mk' (Subgroup.center N) x),
          Additive.ofMul (QuotientGroup.mk' (Subgroup.center N) y)) := Prod.ext hx.symm hy.symm
      have hb : b = (Additive.ofMul (QuotientGroup.mk' (Subgroup.center N) x'),
          Additive.ofMul (QuotientGroup.mk' (Subgroup.center N) y')) := Prod.ext hx'.symm hy'.symm
      rw [ha, hb]
      change Additive.ofMul (QuotientGroup.mk' (commutator N)
          (automorphismCorrection D E (x * x') (y * y'))) =
        Additive.ofMul (QuotientGroup.mk' (commutator N) (automorphismCorrection D E x y) *
          QuotientGroup.mk' (commutator N) (automorphismCorrection D E x' y'))
      rw [automorphismCorrection_mul_of_classTwo hC]
      simp only [map_mul, quotient_commutator_paperCommutator, one_mul, mul_one] }

theorem derivedCorrectionLinear_mem_ker_iff
    (hC : commutator N ≤ Subgroup.center N) (D E : MulAut N)
    (hD : ∀ z ∈ Subgroup.center N, D z = z)
    (hE : ∀ z ∈ Subgroup.center N, E z = z) (a : CorrectionSpace N) :
    a ∈ (derivedCorrectionLinear hC D E hD hE).ker ↔
      quotientCorrection D E hD hE a ∈ commutator N := by
  change QuotientGroup.mk' (commutator N) (quotientCorrection D E hD hE a) = 1 ↔ _
  exact QuotientGroup.eq_one_iff _

def abelianizationCenterProjection (hC : commutator N ≤ Subgroup.center N) :
    Additive (N ⧸ commutator N) →ₗ[ZMod 2] Additive (N ⧸ Subgroup.center N) :=
  (QuotientGroup.map (commutator N) (Subgroup.center N) (MonoidHom.id N) hC).toAdditive.toZModLinearMap 2

theorem abelianizationCenterProjection_surjective
    (hC : commutator N ≤ Subgroup.center N) :
    Function.Surjective (abelianizationCenterProjection hC) := by
  intro z
  obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective (Subgroup.center N) z.toMul
  exact ⟨Additive.ofMul (QuotientGroup.mk' (commutator N) a), ha⟩

theorem centerProjection_derivedCorrectionLinear
    (hC : commutator N ≤ Subgroup.center N) (D E : MulAut N)
    (hD : ∀ z ∈ Subgroup.center N, D z = z)
    (hE : ∀ z ∈ Subgroup.center N, E z = z) :
    (abelianizationCenterProjection hC).comp (derivedCorrectionLinear hC D E hD hE) =
      correctionLinearMap 2 D E := by
  apply LinearMap.ext
  intro a
  exact quotient_centerQuotientCorrection 2 D E hD hE a.1 a.2

theorem derivedCorrectionLinear_ker_le_center_kernel
    (hC : commutator N ≤ Subgroup.center N) (D E : MulAut N)
    (hD : ∀ z ∈ Subgroup.center N, D z = z)
    (hE : ∀ z ∈ Subgroup.center N, E z = z) :
    (derivedCorrectionLinear hC D E hD hE).ker ≤ (correctionLinearMap 2 D E).ker := by
  intro a ha
  change correctionLinearMap 2 D E a = 0
  rw [← centerProjection_derivedCorrectionLinear hC D E hD hE, LinearMap.comp_apply,
    show derivedCorrectionLinear hC D E hD hE a = 0 from ha, map_zero]

end Kourovka2135
