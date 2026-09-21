import Kourovka2135.OddMovingKernelLifting
import Kourovka2135.PerfectMovingKernel

/-! Odd-prime good-set lifting from the canonical central quotient G/[R,G]. -/

set_option autoImplicit false
universe u
namespace Kourovka2135
variable {G : Type u} [Group G] [Finite G] [Group.IsPerfect G]

theorem IsGeneratingGoodSet.preimage_quotient_commutator_of_odd_frattini
    {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (R : Subgroup G) [R.Normal] (hR : IsPGroup p R) (hF : R ≤ frattini G)
    {Y : Set (G ⧸ ⁅R, (⊤ : Subgroup G)⁆)} (hY : IsGeneratingGoodSet Y) :
    IsGeneratingGoodSet ((QuotientGroup.mk' ⁅R, (⊤ : Subgroup G)⁆) ⁻¹' Y) := by
  let D := ⁅R, (⊤ : Subgroup G)⁆
  have hDle : D ≤ R := Subgroup.commutator_le_left _ _
  apply hY.preimage_of_odd_moving_frattini_kernel hp hodd (QuotientGroup.mk' D)
    (QuotientGroup.mk'_surjective D)
  · rw [QuotientGroup.ker_mk']
    exact hR.to_le hDle
  · rw [QuotientGroup.ker_mk']
    exact hDle.trans hF
  · rw [QuotientGroup.ker_mk']
    exact commutator_top_idempotent_of_isPerfect R

end Kourovka2135
