import Kourovka2135.SpecialMinimalCommutatorFiber
import Kourovka2135.GoodSetLifting

/-! Lifting whole generating good sets through special minimal nonabelian
2-kernels. The quotient values must have nontrivial image in the simple quotient. -/
set_option autoImplicit false
namespace Kourovka2135
variable {G : Type*} [Group G] [Finite G] [Group.IsPerfect G]

theorem IsGeneratingGoodSet.preimage_quotient_of_special_minimal
    (N : Subgroup G) [N.Normal] (hN : IsPGroup 2 N)
    (hmin : ∀ H : Subgroup G, H.Normal → H < N → H ≤ Subgroup.center G)
    (hnonabelian : ¬ IsMulCommutative N)
    (hspecial : Subgroup.center N = commutator N) (hFrattini : N ≤ frattini G)
    (R : Subgroup G) [R.Normal] (hR : IsPGroup 2 R) [IsSimpleGroup (G ⧸ R)]
    {Y : Set (G ⧸ N)} (hY : IsGeneratingGoodSet Y)
    (hYnontrivial : ∀ t : G, QuotientGroup.mk' N t ∈ Y → QuotientGroup.mk' R t ≠ 1) :
    IsGeneratingGoodSet ((QuotientGroup.mk' N) ⁻¹' Y) := by
  let q := QuotientGroup.mk' N
  intro t ht
  obtain ⟨α, hα, β, hβ, hαβ, hgen⟩ := hY (q t) ht
  obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective N α
  obtain ⟨b, hb⟩ := QuotientGroup.mk'_surjective N β
  change q a = α at ha
  change q b = β at hb
  have habgen : Subgroup.closure ({a, b} : Set G) = ⊤ := by
    apply closure_pair_eq_top_of_quotient_generation N hFrattini
    change Subgroup.closure ({q a, q b} : Set (G ⧸ N)) = ⊤
    rw [ha, hb]
    exact hgen
  have hc : q (paperCommutator a b) = q t := by
    simpa only [paperCommutator, map_mul, map_inv, ha, hb] using hαβ
  have hc' : QuotientGroup.mk' R (paperCommutator a b) ≠ 1 := by
    apply hYnontrivial
    change q (paperCommutator a b) ∈ Y
    rw [hc]
    exact ht
  have hr : (paperCommutator a b)⁻¹ * t ∈ N := by
    apply (QuotientGroup.eq_one_iff _).mp
    change q ((paperCommutator a b)⁻¹ * t) = 1
    rw [map_mul, map_inv, hc, inv_mul_cancel]
  obtain ⟨u, v, huv⟩ := exists_paperCommutator_mul_eq_of_special_minimal
    N hN hmin hnonabelian hspecial R hR a b habgen hc'
    (⟨(paperCommutator a b)⁻¹ * t, hr⟩ : N)
  have hqu : q (u : G) = 1 := (QuotientGroup.eq_one_iff _).mpr u.property
  have hqv : q (v : G) = 1 := (QuotientGroup.eq_one_iff _).mpr v.property
  have hau : q (a * u) = α := by rw [map_mul, hqu, mul_one]; exact ha
  have hbv : q (b * v) = β := by rw [map_mul, hqv, mul_one]; exact hb
  refine ⟨a * u, ?_, b * v, ?_, ?_, ?_⟩
  · change q (a * u) ∈ Y
    rw [hau]
    exact hα
  · change q (b * v) ∈ Y
    rw [hbv]
    exact hβ
  · simpa only [Subgroup.coe_mk, mul_inv_cancel_left] using huv
  · apply closure_pair_eq_top_of_quotient_generation N hFrattini
    change Subgroup.closure ({q (a * u), q (b * v)} : Set (G ⧸ N)) = ⊤
    rw [hau, hbv]
    exact hgen

end Kourovka2135
