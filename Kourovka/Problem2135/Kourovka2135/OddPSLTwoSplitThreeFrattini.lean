import Kourovka2135.OddSLTwoCenter
import Kourovka2135.OddSplitTorusGoodPair
import Kourovka2135.PerfectCentralProperSolvable
import Kourovka2135.CentralReferenceGoodSet
import Kourovka2135.OddPSLTwoMinimalFiber
import Kourovka2135.PSL27MinimalFiber
import Kourovka2135.GeneratingGoodSetFullFiber

/-! Actual split-order-three good sets through binary Frattini covers.

For an odd finite field of cardinality greater than seven, the actual
split-order-three moving-rank theorem fills the nonabelian minimal fibers.
The central reference is actual SL2 and its center is proved to have size
two. Only the displayed general central-kernel bound remains conditional.
The separate q7 endpoint uses the already proved q7 H1 vanishing instead.
-/

set_option autoImplicit false
noncomputable section
namespace Kourovka2135.OddPSLTwoSplitThreeFrattini

open OddPSLTwoProjectiveChart BinaryFrattiniFullFiberInduction
open BinarySplitTorusGoodPair

variable (F : Type) [Field F] [Finite F]
local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

def goodSet : Set (SLTwo.SL2 F) := splitOrderSet 3
def projectiveGoodSet : Set (Q F) := quotient F '' goodSet F

/-- A genuine order-three field unit supplies the elementary perfectness
witness for SL2; perfectness is not assumed from the sought good set. -/
theorem reference_isPerfect (hsplit : 3 ∣ Nat.card F - 1) :
    Group.IsPerfect (SLTwo.SL2 F) := by
  have hdiv : 3 ∣ Nat.card Fˣ := by rwa [Nat.card_units]
  obtain ⟨r, hr⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) 3 hdiv
  refine ⟨Matrix.SL2.commutator_eq_top (Units.ne_zero r) ?_⟩
  intro hs
  have hs' : r ^ 2 = 1 := Units.ext hs
  have hd := orderOf_dvd_of_pow_eq_one hs'
  rw [hr] at hd
  norm_num at hd

theorem goodSet_nonempty (hsplit : 3 ∣ Nat.card F - 1) : (goodSet F).Nonempty :=
  BinarySplitGoodSetGeneration.splitOrderSet_nonempty F hsplit

theorem isGeneratingGoodSet
    (hsplit : 3 ∣ Nat.card F - 1)
    (hsolv : ∀ H : Subgroup (Q F), H < ⊤ → Group.IsSolvable H) :
    IsGeneratingGoodSet (goodSet F) := by
  let : Group.IsPerfect (SLTwo.SL2 F) := reference_isPerfect F hsplit
  have hs : ∀ H : Subgroup (SLTwo.SL2 F), H < ⊤ → Group.IsSolvable H :=
    PerfectCentralProperSolvable.proper_subgroup_isSolvable (quotient F)
      (by change (QuotientGroup.mk' (Subgroup.center (SLTwo.SL2 F))).ker ≤ _; simp) hsolv
  exact OddSplitTorusGoodPair.isGeneratingGoodSet F hs (by decide) hsplit

theorem projective_isGeneratingGoodSet
    (hsplit : 3 ∣ Nat.card F - 1)
    (hsolv : ∀ H : Subgroup (Q F), H < ⊤ → Group.IsSolvable H) :
    IsGeneratingGoodSet (projectiveGoodSet F) :=
  IsGeneratingGoodSet.image_of_surjective (quotient F)
    (QuotientGroup.mk'_surjective _) (isGeneratingGoodSet F hsplit hsolv)

omit [Finite F] in
/-- Every allowed output is conjugate to an actual split order-three torus
element, in the direction required by the checked fiber theorem. -/
theorem exists_torus_of_mem {g : Q F} (hg : g ∈ projectiveGoodSet F) :
    ∃ r : Fˣ, orderOf r = 3 ∧ IsConj g (OddPSLTwoTorusMovingRank.projectiveTorusHom F r) := by
  obtain ⟨x, hx, rfl⟩ := hg
  obtain ⟨r, hr, hc⟩ := hx
  exact ⟨r, hr, ((quotient F).map_isConj hc).symm⟩

theorem orderOf_mem_projectiveGoodSet (hodd : Odd (Nat.card F))
    {g : Q F} (hg : g ∈ projectiveGoodSet F) : orderOf g = 3 := by
  obtain ⟨x, hx, rfl⟩ := hg
  have hx3 : orderOf x = 3 := orderOf_mem_splitOrderSet hx
  apply orderOf_eq_prime
  · rw [← map_pow]
    have hxpow : x ^ 3 = 1 := by simpa only [hx3] using pow_orderOf_eq_one x
    rw [hxpow, map_one]
  · intro h
    have hc : x ∈ Subgroup.center (SLTwo.SL2 F) := (QuotientGroup.eq_one_iff _).mp h
    have hd := (Subgroup.center (SLTwo.SL2 F)).orderOf_dvd_natCard hc
    rw [hx3, OddSLTwoCenter.card_center F hodd] at hd
    norm_num at hd

theorem reference_good
    (hsplit : 3 ∣ Nat.card F - 1)
    (hsolv : ∀ H : Subgroup (Q F), H < ⊤ → Group.IsSolvable H) :
    HasOddGeneratingGoodSetOver (quotient F) (projectiveGoodSet F) := by
  obtain ⟨g, hg⟩ := goodSet_nonempty F hsplit
  refine ⟨goodSet F, isGeneratingGoodSet F hsplit hsolv, ?_, g, hg, ?_⟩
  · intro x hx
    exact ⟨x, hx, rfl⟩
  · rw [orderOf_mem_splitOrderSet hg]
    decide

/-- The central-cover boundary is the sole temporary structural input. -/
theorem centralBase (hodd : Odd (Nat.card F))
    (hsplit : 3 ∣ Nat.card F - 1)
    (hsolv : ∀ H : Subgroup (Q F), H < ⊤ → Group.IsSolvable H)
    (hbound : CentralDoubleCoverUniqueness.KernelBound (Q F)) :
    CentralBase (Q F) (projectiveGoodSet F) := by
  let : Group.IsPerfect (SLTwo.SL2 F) := reference_isPerfect F hsplit
  exact CentralReferenceGoodSet.centralBase hbound (quotient F)
    (QuotientGroup.mk'_surjective _)
    (by change (QuotientGroup.mk' (Subgroup.center (SLTwo.SL2 F))).ker ≤ _; simp)
    (OddSLTwoCenter.card_ker_quotient F hodd) (projectiveGoodSet F)
    (reference_good F hsplit hsolv)

/-- The actual split-three moving-rank bound fills every required minimal
nonabelian fiber for cardinality greater than seven. -/
theorem minimalNonabelianLift (hodd : Odd (Nat.card F)) (hsize : 7 < Nat.card F) :
    MinimalNonabelianLift (Q F) (projectiveGoodSet F) := by
  let : Fintype F := Fintype.ofFinite F
  intro A _ _ _ π _ hπ hR hRΦ N _ hNR hmin hnonabelian Y hY hsub
  apply hY.preimage_quotient_of_full_fiber N (hNR.trans hRΦ)
  intro a b hgen hc t
  let e := QuotientGroup.quotientKerEquivOfSurjective π hπ
  have himage : e (QuotientGroup.mk' π.ker (paperCommutator a b)) ∈ projectiveGoodSet F :=
    hsub hc
  have hne : QuotientGroup.mk' π.ker (paperCommutator a b) ≠ 1 := by
    intro hz
    have ho := orderOf_mem_projectiveGoodSet F hodd himage
    rw [hz, map_one, orderOf_one] at ho
    norm_num at ho
  obtain ⟨r, hr, hconj⟩ := exists_torus_of_mem F himage
  exact exists_paperCommutator_mul_eq_of_minimal_odd_pslTwo_split_three
    F N (hR.to_le hNR) hmin hnonabelian π.ker hR hRΦ e
    (by simpa only [Nat.card_eq_fintype_card] using hodd)
    (by simpa only [Nat.card_eq_fintype_card] using hsize)
    a b hgen hne r hr hconj t

/-- An actual odd generating good set through every finite perfect binary
Frattini cover, with the central kernel bound displayed explicitly. -/
theorem hasOddGeneratingGoodSetOver (hodd : Odd (Nat.card F))
    (hsize : 7 < Nat.card F) (hsplit : 3 ∣ Nat.card F - 1)
    (hsolv : ∀ H : Subgroup (Q F), H < ⊤ → Group.IsSolvable H)
    (hbound : CentralDoubleCoverUniqueness.KernelBound (Q F))
    {G : Type} [Group G] [Finite G] [Group.IsPerfect G]
    (π : G →* Q F) (hπ : Function.Surjective π)
    (hR : IsPGroup 2 π.ker) (hRΦ : π.ker ≤ frattini G) :
    HasOddGeneratingGoodSetOver π (projectiveGoodSet F) := by
  let : IsSimpleGroup (Q F) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
  exact BinaryFrattiniFullFiberInduction.hasOddGeneratingGoodSetOver (Q F)
    (projectiveGoodSet F) (centralBase F hodd hsplit hsolv hbound)
    (minimalNonabelianLift F hodd hsize) π hπ hR hRΦ

/-- The q7 minimal-kernel theorem replaces the strict size inequality. -/
theorem minimalNonabelianLift_seven :
    MinimalNonabelianLift (Q (ZMod 7)) (projectiveGoodSet (ZMod 7)) := by
  intro A _ _ _ π _ hπ hR hRΦ N _ hNR hmin hnonabelian Y hY hsub
  apply hY.preimage_quotient_of_full_fiber N (hNR.trans hRΦ)
  intro a b hgen hc t
  let e := QuotientGroup.quotientKerEquivOfSurjective π hπ
  have himage : e (QuotientGroup.mk' π.ker (paperCommutator a b)) ∈
      projectiveGoodSet (ZMod 7) := hsub hc
  have hne : QuotientGroup.mk' π.ker (paperCommutator a b) ≠ 1 := by
    intro hz
    have ho := orderOf_mem_projectiveGoodSet (ZMod 7)
      (by norm_num [Nat.card_eq_fintype_card, ZMod.card]) himage
    rw [hz, map_one, orderOf_one] at ho
    norm_num at ho
  exact exists_paperCommutator_mul_eq_of_minimal_psl27
    N (hR.to_le hNR) hmin π.ker hR e hnonabelian hRΦ a b hgen hne t

theorem hasOddGeneratingGoodSetOver_seven
    (hsolv : ∀ H : Subgroup (Q (ZMod 7)), H < ⊤ → Group.IsSolvable H)
    (hbound : CentralDoubleCoverUniqueness.KernelBound (Q (ZMod 7)))
    {G : Type} [Group G] [Finite G] [Group.IsPerfect G]
    (π : G →* Q (ZMod 7)) (hπ : Function.Surjective π)
    (hR : IsPGroup 2 π.ker) (hRΦ : π.ker ≤ frattini G) :
    HasOddGeneratingGoodSetOver π (projectiveGoodSet (ZMod 7)) := by
  let : IsSimpleGroup (Q (ZMod 7)) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by
    norm_num [Nat.card_eq_fintype_card, ZMod.card])
  exact BinaryFrattiniFullFiberInduction.hasOddGeneratingGoodSetOver (Q (ZMod 7))
    (projectiveGoodSet (ZMod 7))
    (centralBase (ZMod 7) (by norm_num [Nat.card_eq_fintype_card, ZMod.card])
      (by norm_num [Nat.card_eq_fintype_card, ZMod.card]) hsolv hbound)
    minimalNonabelianLift_seven π hπ hR hRΦ

end Kourovka2135.OddPSLTwoSplitThreeFrattini
