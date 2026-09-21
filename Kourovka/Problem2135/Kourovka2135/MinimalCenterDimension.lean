import Kourovka2135.DerivedCorrectionLinear
import Kourovka2135.MinimalSpecialKernel

/-! Identification of the actual center-excess dimension with the kernel
of the abelianization-to-center-quotient projection, and its cohomology bound. -/
set_option autoImplicit false
namespace Kourovka2135
open scoped IsMulCommutative

section General
variable {G : Type*} [Group G]

/-- The projection from the abelianization kills exactly the image of the center. -/
theorem abelianizationCenterProjection_ker_eq_centerImageSubmodule
    (N : Subgroup G)
    [IsElementaryAbelian 2 (N ⧸ Subgroup.center N)]
    [IsElementaryAbelian 2 (N ⧸ commutator N)]
    (hC : commutator N ≤ Subgroup.center N) :
    (abelianizationCenterProjection hC).ker = centerImageSubmodule N (commutator N) 2 := by
  apply Submodule.ext
  intro z
  constructor
  · intro hz
    obtain ⟨n, hn⟩ := QuotientGroup.mk'_surjective (commutator N) z.toMul
    have hzn : z = Additive.ofMul (QuotientGroup.mk' (commutator N) n) := hn.symm
    have hncenter : n ∈ Subgroup.center N := by
      apply (QuotientGroup.eq_one_iff _).mp
      rw [hzn] at hz
      exact hz
    exact ⟨n, hncenter, hn⟩
  · rintro ⟨n, hncenter, hn⟩
    change abelianizationCenterProjection hC (Additive.ofMul z.toMul) = 0
    rw [← hn]
    change QuotientGroup.mk' (Subgroup.center N) n = 1
    exact (QuotientGroup.eq_one_iff _).mpr hncenter

/-- The difference of the actual quotient dimensions is the image-of-center dimension. -/
theorem abelianization_center_finrank_difference_eq_centerImage
    (N : Subgroup G) [Finite N]
    [IsElementaryAbelian 2 (N ⧸ Subgroup.center N)]
    [IsElementaryAbelian 2 (N ⧸ commutator N)]
    (hC : commutator N ≤ Subgroup.center N) :
    Module.finrank (ZMod 2) (Additive (N ⧸ commutator N)) -
        Module.finrank (ZMod 2) (Additive (N ⧸ Subgroup.center N)) =
      Module.finrank (ZMod 2) (centerImageSubmodule N (commutator N) 2) := by
  have h := (abelianizationCenterProjection hC).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (abelianizationCenterProjection_surjective hC),
    finrank_top, abelianizationCenterProjection_ker_eq_centerImageSubmodule N hC] at h
  omega

end General

section Cohomology
variable {G : Type} [Group G] [Finite G] [Group.IsPerfect G]

/-- The numeric center excess in the correction rank criterion is bounded
by the already constructed actual quotient-module first cohomology. -/
theorem minimal_abelianization_center_finrank_difference_le_h1
    (N : Subgroup G) [N.Normal] (hN : IsPGroup 2 N)
    (hnonabelian : ¬ IsMulCommutative N)
    (hmin : ∀ H : Subgroup G, H.Normal → H < N → H ≤ Subgroup.center G)
    (R : Subgroup G) [R.Normal] (hR : IsPGroup 2 R) (hRΦ : R ≤ frattini G)
    [IsElementaryAbelian 2 (N ⧸ commutator N)]
    [IsElementaryAbelian 2 (N ⧸ Subgroup.center N)] :
    Module.finrank (ZMod 2) (Additive (N ⧸ commutator N)) -
        Module.finrank (ZMod 2) (Additive (N ⧸ Subgroup.center N)) ≤
      Module.finrank (ZMod 2) (groupCohomology
        (Rep.of (minimalCenterQuotientRepresentation N hN hnonabelian hmin R hR hRΦ).dual) 1) := by
  let : Group.IsNilpotent N := hN.isNilpotent
  have hnoncentral : ¬ N ≤ Subgroup.center G := by
    intro h
    apply hnonabelian
    exact ⟨⟨fun a b => Subtype.ext (Subgroup.mem_center_iff.mp (h b.property) a)⟩⟩
  rw [abelianization_center_finrank_difference_eq_centerImage N
    (minimal_noncentral_commutator_le_internal_center N hmin)]
  exact minimal_center_excess_finrank_le_h1 N hN hnonabelian hmin R hR hRΦ hnoncentral

end Cohomology
end Kourovka2135
