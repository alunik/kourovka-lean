import Kourovka2135.OddFrattiniKernel
import Kourovka2135.GoodSetLifting

/-! The abelian good-set correction step is available in every odd-prime Frattini kernel of a finite perfect group. -/

set_option autoImplicit false
universe u
namespace Kourovka2135
variable {G : Type u} [Group G] [Finite G] [Group.IsPerfect G]

theorem exists_abelian_normal_moving_subgroup_of_odd_frattini
    {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (R : Subgroup G) [R.Normal] (hR : IsPGroup p R)
    (hFrattini : R ≤ frattini G) (hnoncentral : ¬ R ≤ Subgroup.center G) :
    ∃ N : Subgroup G, N ≤ R ∧ N.Normal ∧ ¬ N ≤ Subgroup.center G ∧
      IsMulCommutative N ∧ ⁅N, (⊤ : Subgroup G)⁆ = N := by
  obtain ⟨N, hNR, hnormal, hnc, hmin⟩ := exists_minimal_normal_noncentral R hnoncentral
  let : N.Normal := hnormal
  have hN : IsPGroup p N := hR.of_injective (Subgroup.inclusion hNR)
    (Subgroup.inclusion_injective hNR)
  exact ⟨N, hNR, hnormal, hnc,
    minimal_noncentral_odd_frattini_isMulCommutative hp hodd N hN
      (hNR.trans hFrattini) hnc hmin,
    commutator_eq_self_of_minimal_noncentral N hnc hmin⟩

theorem IsGeneratingGoodSet.preimage_quotient_of_minimal_noncentral_odd
    {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (N : Subgroup G) [N.Normal] (hN : IsPGroup p N)
    (hFrattini : N ≤ frattini G) (hnoncentral : ¬ N ≤ Subgroup.center G)
    (hmin : ∀ M : Subgroup G, M.Normal → M < N → M ≤ Subgroup.center G)
    {Y : Set (G ⧸ N)} (hY : IsGeneratingGoodSet Y) :
    IsGeneratingGoodSet ((QuotientGroup.mk' N) ⁻¹' Y) := by
  let : IsMulCommutative N := minimal_noncentral_odd_frattini_isMulCommutative
    hp hodd N hN hFrattini hnoncentral hmin
  exact hY.preimage_quotient_of_abelian N hFrattini
    (commutator_eq_self_of_minimal_noncentral N hnoncentral hmin)

end Kourovka2135
