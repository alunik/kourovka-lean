import Kourovka2135.BinaryFrattiniSplitGoodSet
import Kourovka2135.BinarySplitGoodSetObstruction

/-! Product-order obstruction for every binary Frattini cover of an actual
minimal-simple SL2(2^f), f at least three. The good-set construction and
concrete root-subgroup contradiction are both discharged. No noncentral
radical hypothesis or character, fiber, or generation assumption remains.
-/

set_option autoImplicit false

namespace Kourovka2135

theorem not_productOrderCondition_of_binary_frattini_slTwo
    {F : Type} [Field F] [Fintype F] [CharP F 2]
    [IsSimpleGroup (SLTwo.SL2 F)]
    (f : ℕ) (hcard : Fintype.card F = 2 ^ f) (hf : 3 ≤ f)
    (hsolv : ∀ H : Subgroup (SLTwo.SL2 F), H < ⊤ → Group.IsSolvable H)
    {G : Type} [Group G] [Finite G] [Group.IsPerfect G]
    (pi : G →* SLTwo.SL2 F) (hpi : Function.Surjective pi)
    (hR : IsPGroup 2 pi.ker) (hRΦ : pi.ker ≤ frattini G) (w : OuterWord) :
    ¬ ProductOrderCondition w 2 G := by
  obtain ⟨r, hr, hrOdd, hrSplit⟩ :=
    BinaryFrattiniSplitGoodSet.exists_odd_prime_dvd_two_pow_sub_one f hf
  let : Fact r.Prime := ⟨hr⟩
  have hrSplit' : r ∣ Nat.card F - 1 := by
    simpa only [Nat.card_eq_fintype_card, hcard] using hrSplit
  exact BinarySplitGoodSetObstruction.not_productOrderCondition pi hpi hR r hr
    (BinaryFrattiniSplitGoodSet.hasOddGeneratingGoodSetOver
      f hcard hf hsolv r hrOdd hrSplit' pi hpi hR hRΦ) w

end Kourovka2135
