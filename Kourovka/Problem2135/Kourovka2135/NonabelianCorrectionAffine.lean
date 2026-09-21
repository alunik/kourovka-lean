import Kourovka2135.NonabelianCorrectionQuadratic

/-! Normalizing the actual group correction on every affine linear fiber.
The normalization adds an explicitly verified linear term. -/
set_option autoImplicit false
namespace Kourovka2135
open scoped IsMulCommutative
variable {N : Type*} [Group N]
variable [IsElementaryAbelian 2 (N ⧸ Subgroup.center N)]
variable [IsElementaryAbelian 2 (commutator N)]
variable [IsElementaryAbelian 2 (Subgroup.center N)]

def affineCorrectionQuadratic (hC : commutator N ≤ Subgroup.center N)
    (D E : MulAut N)
    (hD : ∀ z ∈ Subgroup.center N, D z = z)
    (hE : ∀ z ∈ Subgroup.center N, E z = z) (b : CorrectionSpace N) :
    QuadraticMap (ZMod 2) (correctionLinearMap 2 D E).ker
      (Additive (Subgroup.center N)) where
  toFun a := centralCorrection D E hD hE a + correctionBilinear hC D E a b
  toFun_smul r a := by
    have hr : r = 0 ∨ r = 1 := by
      fin_cases r
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases hr with rfl | rfl
    · simp only [zero_smul, zero_mul, Submodule.coe_zero,
        centralCorrection_zero, map_zero, LinearMap.zero_apply, add_zero]
    · simp only [one_smul, one_mul]
  exists_companion' := by
    refine ⟨(correctionBilinear hC D E).compl₁₂
      (correctionLinearMap 2 D E).ker.subtype (correctionLinearMap 2 D E).ker.subtype, ?_⟩
    intro a a'
    change centralCorrection D E hD hE (a + a') +
      correctionBilinear hC D E ((a : CorrectionSpace N) + a') b = _
    rw [centralCorrection_add hC, map_add, LinearMap.add_apply]
    change _ = (centralCorrection D E hD hE a + correctionBilinear hC D E a b) +
      (centralCorrection D E hD hE a' + correctionBilinear hC D E a' b) +
      correctionBilinear hC D E a a'
    abel

theorem affineCorrectionQuadratic_polar (hC : commutator N ≤ Subgroup.center N)
    (D E : MulAut N)
    (hD : ∀ z ∈ Subgroup.center N, D z = z)
    (hE : ∀ z ∈ Subgroup.center N, E z = z) (b : CorrectionSpace N)
    (a a' : (correctionLinearMap 2 D E).ker) :
    (affineCorrectionQuadratic hC D E hD hE b).polarBilin a a' =
      correctionBilinear hC D E a a' := by
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar]
  change (centralCorrection D E hD hE (a + a') +
      correctionBilinear hC D E ((a : CorrectionSpace N) + a') b) -
    (centralCorrection D E hD hE a + correctionBilinear hC D E a b) -
    (centralCorrection D E hD hE a' + correctionBilinear hC D E a' b) = _
  rw [centralCorrection_add hC, map_add, LinearMap.add_apply]
  abel

theorem quotientCorrection_add_eq_affine (hC : commutator N ≤ Subgroup.center N)
    (D E : MulAut N)
    (hD : ∀ z ∈ Subgroup.center N, D z = z)
    (hE : ∀ z ∈ Subgroup.center N, E z = z) (b : CorrectionSpace N)
    (a : (correctionLinearMap 2 D E).ker) :
    quotientCorrection D E hD hE (b + a) = quotientCorrection D E hD hE b *
      (((affineCorrectionQuadratic hC D E hD hE b) a).toMul : N) := by
  rw [add_comm b, quotientCorrection_add_of_mem_ker hC D E hD hE _ _ a.property]
  change quotientCorrection D E hD hE a * quotientCorrection D E hD hE b *
      ((correctionBilinear hC D E a b).toMul : N) =
    quotientCorrection D E hD hE b *
      (quotientCorrection D E hD hE a * ((correctionBilinear hC D E a b).toMul : N))
  rw [← mul_assoc]
  exact congrArg (fun z : N => z * ((correctionBilinear hC D E a b).toMul : N))
    (Subgroup.mem_center_iff.mp (quotientCorrection_mem_center D E hD hE a.property) _).symm

theorem quotientCorrection_surjective_of_affine_surjective
    (hC : commutator N ≤ Subgroup.center N) (D E : MulAut N)
    (hD : ∀ z ∈ Subgroup.center N, D z = z)
    (hE : ∀ z ∈ Subgroup.center N, E z = z)
    (hL : Function.Surjective (correctionLinearMap 2 D E))
    (hQ : ∀ b : CorrectionSpace N,
      Function.Surjective (affineCorrectionQuadratic hC D E hD hE b)) :
    Function.Surjective (quotientCorrection D E hD hE) := by
  intro n
  obtain ⟨b, hb⟩ := hL (Additive.ofMul (QuotientGroup.mk' (Subgroup.center N) n))
  have hf : QuotientGroup.mk' (Subgroup.center N) (quotientCorrection D E hD hE b) =
      QuotientGroup.mk' (Subgroup.center N) n := by
    have hh := quotient_centerQuotientCorrection 2 D E hD hE b.1 b.2
    exact hh.trans hb
  have hz : (quotientCorrection D E hD hE b)⁻¹ * n ∈ Subgroup.center N := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' (Subgroup.center N)
      ((quotientCorrection D E hD hE b)⁻¹ * n) = 1
    rw [map_mul, map_inv, hf, inv_mul_cancel]
  obtain ⟨a, ha⟩ := hQ b (Additive.ofMul ⟨_, hz⟩)
  refine ⟨b + a, ?_⟩
  rw [quotientCorrection_add_eq_affine hC D E hD hE b a, ha]
  exact mul_inv_cancel_left _ _

theorem automorphismCorrection_surjective_of_quotient
    (D E : MulAut N)
    (hD : ∀ z ∈ Subgroup.center N, D z = z)
    (hE : ∀ z ∈ Subgroup.center N, E z = z)
    (hF : Function.Surjective (quotientCorrection D E hD hE)) (n : N) :
    ∃ x y : N, automorphismCorrection D E x y = n := by
  obtain ⟨b, hb⟩ := hF n
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (Subgroup.center N) b.1.toMul
  obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective (Subgroup.center N) b.2.toMul
  refine ⟨x, y, ?_⟩
  change centerQuotientCorrection D E hD hE
    (QuotientGroup.mk' (Subgroup.center N) x) (QuotientGroup.mk' (Subgroup.center N) y) = n
  rw [hx, hy]
  exact hb

end Kourovka2135
