import Kourovka2135.DerivedCorrectionQuadratic
import Kourovka2135.NonabelianCorrectionSurjective

/-! Surjectivity of the actual correction modulo the derived subgroup and
assembly of all its derived-valued affine fibers. -/
set_option autoImplicit false
universe u
namespace Kourovka2135
open scoped IsMulCommutative
open AbelianDifference
variable {G : Type u} [Group G]

/-- A generating ambient pair moves the entire abelianization, so the actual
correction modulo the derived subgroup is surjective. -/
theorem derivedCorrectionLinear_surjective_of_generating_pair
    (N : Subgroup G) [N.Normal]
    [IsElementaryAbelian 2 (N ⧸ Subgroup.center N)]
    [IsElementaryAbelian 2 (N ⧸ commutator N)]
    (hC : commutator N ≤ Subgroup.center N)
    (a b : G) (hgen : Subgroup.closure ({a, b} : Set G) = ⊤)
    (hmove : ⁅N, (⊤ : Subgroup G)⁆ = N)
    (hD : ∀ z ∈ Subgroup.center N,
      (MulAut.conjNormal (a * paperCommutator a b)⁻¹) z = z)
    (hE : ∀ z ∈ Subgroup.center N,
      (MulAut.conjNormal ((paperCommutator a b)⁻¹ * b)⁻¹) z = z) :
    Function.Surjective
      (derivedCorrectionLinear hC
        ((MulAut.conjNormal : G →* MulAut N) (a * paperCommutator a b)⁻¹)
        ((MulAut.conjNormal : G →* MulAut N) ((paperCommutator a b)⁻¹ * b)⁻¹) hD hE) := by
  let ρ := normalQuotientAut N (commutator N)
  let c := paperCommutator a b
  have hpair : Subgroup.closure ({(c⁻¹ * b)⁻¹, (a * c)⁻¹} : Set G) = ⊤ := by
    rw [closure_inverse_pair, closure_commutator_correction_pair, hgen]
  intro t
  obtain ⟨x, z, hxz⟩ := exists_delta_mul_delta_of_generating_pair ρ
    (c⁻¹ * b)⁻¹ (a * c)⁻¹ hpair
    (iSup_normalQuotient_moving_eq_top N (commutator N) hmove) t.toMul
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (commutator N) x
  obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective (commutator N) z
  refine ⟨(Additive.ofMul (QuotientGroup.mk' (Subgroup.center N) u),
    Additive.ofMul (QuotientGroup.mk' (Subgroup.center N) v⁻¹)), ?_⟩
  change QuotientGroup.mk' (commutator N)
      (automorphismCorrection (MulAut.conjNormal (a * c)⁻¹)
        (MulAut.conjNormal (c⁻¹ * b)⁻¹) u v⁻¹) = t.toMul
  simp only [automorphismCorrection,
    (MulAut.conjNormal (a * c)⁻¹ : MulAut N).map_inv,
    (QuotientGroup.mk' (commutator N)).map_mul,
    (QuotientGroup.mk' (commutator N)).map_inv, inv_inv]
  simp only [ρ, delta_apply, normalQuotientAut_apply_mk] at hxz
  convert hxz using 1
  ac_rfl

variable {N : Type*} [Group N]
variable [IsElementaryAbelian 2 (N ⧸ Subgroup.center N)]
variable [IsElementaryAbelian 2 (N ⧸ commutator N)]
variable [IsElementaryAbelian 2 (commutator N)]

/-- Surjectivity of the linear projection and every normalized derived-valued
fiber gives surjectivity of the full group correction. -/
theorem quotientCorrection_surjective_of_derivedAffine_surjective
    (hC : commutator N ≤ Subgroup.center N) (D E : MulAut N)
    (hD : ∀ z ∈ Subgroup.center N, D z = z)
    (hE : ∀ z ∈ Subgroup.center N, E z = z)
    (hA : Function.Surjective (derivedCorrectionLinear hC D E hD hE))
    (hQ : ∀ b : CorrectionSpace N,
      Function.Surjective (derivedAffineCorrectionQuadratic hC D E hD hE b)) :
    Function.Surjective (quotientCorrection D E hD hE) := by
  intro n
  obtain ⟨b, hb⟩ := hA (Additive.ofMul (QuotientGroup.mk' (commutator N) n))
  have hf : QuotientGroup.mk' (commutator N) (quotientCorrection D E hD hE b) =
      QuotientGroup.mk' (commutator N) n := hb
  have hz : (quotientCorrection D E hD hE b)⁻¹ * n ∈ commutator N := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' (commutator N)
      ((quotientCorrection D E hD hE b)⁻¹ * n) = 1
    rw [map_mul, map_inv, hf, inv_mul_cancel]
  obtain ⟨a, ha⟩ := hQ b (Additive.ofMul ⟨_, hz⟩)
  refine ⟨b + a, ?_⟩
  rw [quotientCorrection_add_eq_derivedAffine hC D E hD hE b a, ha]
  exact mul_inv_cancel_left _ _

end Kourovka2135
