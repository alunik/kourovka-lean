import Kourovka2135.SuzukiEightPairedCentralKernel
import Kourovka2135.CentralMaximalGoodSet
import Kourovka2135.SuzukiEightCentralKernel
import Kourovka2135.SuzukiSplitGoodSet
import Kourovka2135.CoprimePGroupLift

/-! An actual generating good set for every perfect central binary cover of
Sz(8). The reference is the paired matrix cover with its proved four-element
kernel; comparison uses the independently proved uniform kernel bound. -/

set_option autoImplicit false
noncomputable section
namespace Kourovka2135.SuzukiEightCentralBase

open SuzukiEightPairedGoodSet SuzukiEightPairedProjection
open SuzukiEightPairedCentralKernel
open BinaryFrattiniFullFiberInduction

theorem image_order {g : E} (hg : g ∈ Y) : orderOf (projection g) = 7 := by
  let e := QuotientGroup.quotientKerEquivOfSurjective projection projection_surjective
  change orderOf (e (QuotientGroup.mk' projection.ker g)) = 7
  rw [e.orderOf_eq,
    orderOf_quotient_eq_of_coprime_pgroup Nat.prime_two projection.ker kernel_binary g]
  · exact orderOf_mem_Y hg
  · rw [orderOf_mem_Y hg]
    decide

theorem reference_good :
    HasOddGeneratingGoodSetOver projection (SuzukiSplitGoodSet.orderSet 1 7) := by
  refine ⟨Y, goodSet, fun _ hg => image_order hg, xE,
    mem_automorphismOrbit xE, ?_⟩
  rw [orderOf_xE]
  decide

theorem kernel_bound : CentralMaximalCover.KernelBound 2 4 (SuzukiGeometry.G 1) := by
  intro D _ _ _ pi hpi hc hp
  exact SuzukiEightCentralKernel.global_card_kernel_le_four pi hpi hc hp

theorem centralBase :
    CentralBase (SuzukiGeometry.G 1) (SuzukiSplitGoodSet.orderSet 1 7) :=
  CentralMaximalGoodSet.centralBase 4 kernel_bound projection projection_surjective
    kernel_central kernel_binary card_kernel _ reference_good

end Kourovka2135.SuzukiEightCentralBase
