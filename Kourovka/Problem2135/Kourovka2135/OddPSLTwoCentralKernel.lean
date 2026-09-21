import Kourovka2135.OddPSLTwoSplitCentralKernel
import Kourovka2135.OddPSLTwoNonsplitCentralKernel
import Kourovka2135.CentralDoubleCoverUniqueness

/-! Every finite perfect central binary cover of actual PSL2 over an odd
finite field has kernel of size at most two. The proof uses the actual split
or nonsplit dihedral subgroup according to the field cardinality modulo four. -/

set_option autoImplicit false
noncomputable section
namespace Kourovka2135.OddPSLTwoCentralKernel
open OddPSLTwoProjectiveChart

theorem card_ker_le_two (F : Type*) [Field F] [Finite F]
    (hodd : Odd (Nat.card F))
    {G : Type*} [Group G] [Finite G] [Group.IsPerfect G]
    (π : G →* Q F) (hπ : Function.Surjective π)
    (hbinary : IsPGroup 2 π.ker) (hcentral : π.ker ≤ Subgroup.center G) :
    Nat.card π.ker ≤ 2 := by
  have hm : Nat.card F % 4 = 1 ∨ Nat.card F % 4 = 3 := by
    obtain ⟨k, hk⟩ := hodd
    omega
  rcases hm with hm | hm
  · exact OddPSLTwoSplitCentralKernel.card_ker_le_two F hm π hπ hbinary hcentral
  · exact OddPSLTwoNonsplitCentralKernel.card_ker_le_two F hm π hπ hbinary hcentral

theorem kernelBound (F : Type) [Field F] [Finite F] (hodd : Odd (Nat.card F)) :
    CentralDoubleCoverUniqueness.KernelBound (Q F) := by
  intro G _ _ _ π hπ hc hp
  exact card_ker_le_two F hodd π hπ hp hc

end Kourovka2135.OddPSLTwoCentralKernel
