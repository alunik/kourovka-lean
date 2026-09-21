import Kourovka2135.OddSLTwoCenter
import Kourovka2135.OddSplitTorusGoodPair
import Kourovka2135.PerfectCentralProperSolvable
import Kourovka2135.CentralReferenceGoodSet
import Kourovka2135.OddPSLTwoMinimalFiber
import Kourovka2135.GeneratingGoodSetFullFiber

/-! Actual odd split-prime good sets through binary Frattini covers.

For field cardinality at least seventeen, the Brandl pair supplies actual
generators conjugate to a power of each allowed output. The power is
(r-1)/2, obtained inside the actual odd cyclic subgroup. Thus the proved
generating-power moving-rank bound applies without a same-class assumption.
The general central binary kernel bound remains an explicit input.
-/

set_option autoImplicit false
noncomputable section
namespace Kourovka2135.OddPSLTwoSplitPrimeFrattini

open OddPSLTwoProjectiveChart BinaryFrattiniFullFiberInduction
open BinarySplitTorusGoodPair

variable (F : Type) [Field F] [Finite F] (r : ℕ) [Fact r.Prime]

def goodSet : Set (SLTwo.SL2 F) := splitOrderSet r
def projectiveGoodSet : Set (Q F) := quotient F '' goodSet F r

private theorem not_dvd_two (hrOdd : Odd r) : ¬ r ∣ 2 := by
  intro h
  rcases (Nat.dvd_prime Nat.prime_two).mp h with h1 | h2
  · exact (Fact.out : r.Prime).ne_one h1
  · rw [h2] at hrOdd
    exact (by decide : ¬ Odd 2) hrOdd

theorem reference_isPerfect (hrOdd : Odd r) (hsplit : r ∣ Nat.card F - 1) :
    Group.IsPerfect (SLTwo.SL2 F) := by
  have hdiv : r ∣ Nat.card Fˣ := by rwa [Nat.card_units]
  obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) r hdiv
  refine ⟨Matrix.SL2.commutator_eq_top (Units.ne_zero v) ?_⟩
  intro hs
  have hs' : v ^ 2 = 1 := Units.ext hs
  have hd := orderOf_dvd_of_pow_eq_one hs'
  rw [hv] at hd
  exact not_dvd_two r hrOdd hd

theorem proper_reference_subgroup_isSolvable (hrOdd : Odd r)
    (hsplit : r ∣ Nat.card F - 1)
    (hsolv : ∀ H : Subgroup (Q F), H < ⊤ → Group.IsSolvable H) :
    ∀ H : Subgroup (SLTwo.SL2 F), H < ⊤ → Group.IsSolvable H := by
  let : Group.IsPerfect (SLTwo.SL2 F) := reference_isPerfect F r hrOdd hsplit
  exact PerfectCentralProperSolvable.proper_subgroup_isSolvable (quotient F)
    (by change (QuotientGroup.mk' (Subgroup.center (SLTwo.SL2 F))).ker ≤ _; simp) hsolv

theorem isGeneratingGoodSet (hrOdd : Odd r) (hsplit : r ∣ Nat.card F - 1)
    (hsolv : ∀ H : Subgroup (Q F), H < ⊤ → Group.IsSolvable H) :
    IsGeneratingGoodSet (goodSet F r) :=
  OddSplitTorusGoodPair.isGeneratingGoodSet F
    (proper_reference_subgroup_isSolvable F r hrOdd hsplit hsolv) hrOdd hsplit

theorem goodSet_nonempty (hsplit : r ∣ Nat.card F - 1) : (goodSet F r).Nonempty :=
  BinarySplitGoodSetGeneration.splitOrderSet_nonempty F hsplit

theorem orderOf_mem_projectiveGoodSet (hodd : Odd (Nat.card F)) (hrOdd : Odd r)
    {g : Q F} (hg : g ∈ projectiveGoodSet F r) : orderOf g = r := by
  obtain ⟨x, hx, rfl⟩ := hg
  have hxr : orderOf x = r := orderOf_mem_splitOrderSet hx
  apply orderOf_eq_prime
  · rw [← map_pow]
    have hxpow : x ^ r = 1 := by simpa only [hxr] using pow_orderOf_eq_one x
    rw [hxpow, map_one]
  · intro h
    have hc : x ∈ Subgroup.center (SLTwo.SL2 F) := (QuotientGroup.eq_one_iff _).mp h
    have hd := (Subgroup.center (SLTwo.SL2 F)).orderOf_dvd_natCard hc
    rw [hxr, OddSLTwoCenter.card_center F hodd] at hd
    exact not_dvd_two r hrOdd hd

/-- Actual generators are conjugate to a specified power of each allowed
output. The output need not itself lie in one fixed conjugacy class. -/
theorem generating_power_pair (hrOdd : Odd r) (hsplit : r ∣ Nat.card F - 1)
    (hsolv : ∀ H : Subgroup (Q F), H < ⊤ → Group.IsSolvable H)
    {g : Q F} (hg : g ∈ projectiveGoodSet F r) :
    ∃ α β : Q F, Subgroup.closure ({α, β} : Set (Q F)) = ⊤ ∧
      IsConj α (g ^ ((r - 1) / 2)) ∧ IsConj β (g ^ ((r - 1) / 2)) := by
  obtain ⟨x, hx, rfl⟩ := hg
  obtain ⟨v, hv, hvx⟩ := hx
  obtain ⟨u, hu, horder⟩ := OddSplitTorusGoodPair.exists_odd_cyclic_square_root v
    (hv ▸ hrOdd)
  have hur : orderOf u = r := horder.trans hv
  have hvne : v ≠ 1 := by
    intro he
    have hh := hv
    rw [he, orderOf_one] at hh
    exact (Fact.out : r.Prime).ne_one hh.symm
  have hd : eigenDifference u ≠ 0 := by
    intro hz
    have he : u⁻¹ = u := Units.ext (sub_eq_zero.mp hz)
    have hs : u ^ 2 = 1 := by
      calc
        u ^ 2 = u * u := pow_two _
        _ = u⁻¹ * u := congrArg (fun z => z * u) he.symm
        _ = 1 := inv_mul_cancel _
    exact hvne (hu.symm.trans hs)
  have hm : 2 * ((r - 1) / 2) + 1 = r := by
    obtain ⟨k, hk⟩ := hrOdd
    omega
  have hpow : v ^ ((r - 1) / 2) = u⁻¹ := by
    apply eq_inv_iff_mul_eq_one.mpr
    rw [← hu, ← pow_mul, ← pow_succ, hm, ← hur]
    exact pow_orderOf_eq_one u
  have htor : (SLTwo.tor v) ^ ((r - 1) / 2) = SLTwo.tor u⁻¹ := by
    change (SLTwo.torHom F v) ^ ((r - 1) / 2) = SLTwo.torHom F u⁻¹
    rw [← map_pow, hpow]
  have ha : orderOf (pairLeft u) = r :=
    (orderOf_mem_splitOrderSet (pairLeft_mem_splitOrderSet u)).trans hur
  have hb : orderOf (pairRight u) = r :=
    (orderOf_mem_splitOrderSet (pairRight_mem_splitOrderSet u hd)).trans hur
  have hc : orderOf (paperCommutator (pairLeft u) (pairRight u)) = r := by
    rw [pair_commutator, hu, orderOf_tor, hv]
  have hgen := BinarySplitGoodSetGeneration.generates_of_three_prime_orders F
    (proper_reference_subgroup_isSolvable F r hrOdd hsplit hsolv)
    hrOdd hsplit (pairLeft u) (pairRight u) ha hb hc
  have hleft : IsConj (pairLeft u) (x ^ ((r - 1) / 2)) := by
    have h := (pairLeft_isConj u).symm
    rw [← htor] at h
    exact h.trans (IsConj.pow _ hvx)
  have hright : IsConj (pairRight u) (x ^ ((r - 1) / 2)) := by
    have h := (pairRight_isConj u hd).symm
    rw [← htor] at h
    exact h.trans (IsConj.pow _ hvx)
  refine ⟨quotient F (pairLeft u), quotient F (pairRight u), ?_, ?_, ?_⟩
  · rw [← Set.image_pair, ← MonoidHom.map_closure, hgen]
    exact Subgroup.map_top_of_surjective (quotient F) (QuotientGroup.mk'_surjective _)
  · simpa only [map_pow] using (quotient F).map_isConj hleft
  · simpa only [map_pow] using (quotient F).map_isConj hright

theorem reference_good (hrOdd : Odd r) (hsplit : r ∣ Nat.card F - 1)
    (hsolv : ∀ H : Subgroup (Q F), H < ⊤ → Group.IsSolvable H) :
    HasOddGeneratingGoodSetOver (quotient F) (projectiveGoodSet F r) := by
  obtain ⟨g, hg⟩ := goodSet_nonempty F r hsplit
  refine ⟨goodSet F r, isGeneratingGoodSet F r hrOdd hsplit hsolv, ?_, g, hg, ?_⟩
  · intro x hx
    exact ⟨x, hx, rfl⟩
  · rw [orderOf_mem_splitOrderSet hg]
    exact hrOdd

theorem centralBase (hodd : Odd (Nat.card F)) (hrOdd : Odd r)
    (hsplit : r ∣ Nat.card F - 1)
    (hsolv : ∀ H : Subgroup (Q F), H < ⊤ → Group.IsSolvable H)
    (hbound : CentralDoubleCoverUniqueness.KernelBound (Q F)) :
    CentralBase (Q F) (projectiveGoodSet F r) := by
  let : Group.IsPerfect (SLTwo.SL2 F) := reference_isPerfect F r hrOdd hsplit
  exact CentralReferenceGoodSet.centralBase hbound (quotient F)
    (QuotientGroup.mk'_surjective _)
    (by change (QuotientGroup.mk' (Subgroup.center (SLTwo.SL2 F))).ker ≤ _; simp)
    (OddSLTwoCenter.card_ker_quotient F hodd) (projectiveGoodSet F r)
    (reference_good F r hrOdd hsplit hsolv)

theorem minimalNonabelianLift (hodd : Odd (Nat.card F)) (hsize : 17 ≤ Nat.card F)
    (hrOdd : Odd r) (hsplit : r ∣ Nat.card F - 1)
    (hsolv : ∀ H : Subgroup (Q F), H < ⊤ → Group.IsSolvable H) :
    MinimalNonabelianLift (Q F) (projectiveGoodSet F r) := by
  let : Fintype F := Fintype.ofFinite F
  intro A _ _ _ π _ hπ hR hRΦ N _ hNR hmin hnonabelian Y hY hsub
  apply hY.preimage_quotient_of_full_fiber N (hNR.trans hRΦ)
  intro a b hgen hc t
  let e := QuotientGroup.quotientKerEquivOfSurjective π hπ
  have himage : e (QuotientGroup.mk' π.ker (paperCommutator a b)) ∈
      projectiveGoodSet F r := hsub hc
  have hne : QuotientGroup.mk' π.ker (paperCommutator a b) ≠ 1 := by
    intro hz
    have ho := orderOf_mem_projectiveGoodSet F r hodd hrOdd himage
    rw [hz, map_one, orderOf_one] at ho
    exact (Fact.out : r.Prime).ne_one ho.symm
  obtain ⟨α, β, hpair, hα, hβ⟩ := generating_power_pair F r hrOdd hsplit hsolv himage
  exact exists_paperCommutator_mul_eq_of_minimal_odd_pslTwo_generating_powers
    F N (hR.to_le hNR) hmin hnonabelian π.ker hR hRΦ e
    (by simpa only [Nat.card_eq_fintype_card] using hodd)
    (by simpa only [Nat.card_eq_fintype_card] using hsize)
    a b hgen hne α β hpair ((r - 1) / 2) ((r - 1) / 2) hα hβ t

/-- The full actual Frattini invariant; only the displayed family inputs
remain, with no assumed generation, fiber, or representation classification. -/
theorem hasOddGeneratingGoodSetOver (hodd : Odd (Nat.card F))
    (hsize : 17 ≤ Nat.card F) (hrOdd : Odd r) (hsplit : r ∣ Nat.card F - 1)
    (hsolv : ∀ H : Subgroup (Q F), H < ⊤ → Group.IsSolvable H)
    (hbound : CentralDoubleCoverUniqueness.KernelBound (Q F))
    {G : Type} [Group G] [Finite G] [Group.IsPerfect G]
    (π : G →* Q F) (hπ : Function.Surjective π)
    (hR : IsPGroup 2 π.ker) (hRΦ : π.ker ≤ frattini G) :
    HasOddGeneratingGoodSetOver π (projectiveGoodSet F r) := by
  let : IsSimpleGroup (Q F) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
  exact BinaryFrattiniFullFiberInduction.hasOddGeneratingGoodSetOver (Q F)
    (projectiveGoodSet F r) (centralBase F r hodd hrOdd hsplit hsolv hbound)
    (minimalNonabelianLift F r hodd hsize hrOdd hsplit hsolv) π hπ hR hRΦ

end Kourovka2135.OddPSLTwoSplitPrimeFrattini
