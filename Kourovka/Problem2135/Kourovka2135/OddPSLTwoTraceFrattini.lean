import Kourovka2135.SLTwoTraceGoodSetProjective
import Kourovka2135.OddPSLTwoCentralObstruction
import Kourovka2135.OddPSLTwoMinimalFiber
import Kourovka2135.GeneratingGoodSetFullFiber

/-! Concrete broad-trace good-set lifting. The matrix generation and
conjugate-power pair inputs are separated from the already proved full
Frattini induction; no module bound or kernel size is assumed. -/

set_option autoImplicit false
noncomputable section
namespace Kourovka2135.OddPSLTwoTraceFrattini
open OddPSLTwoProjectiveChart SLTwoTraceGoodSet SLTwoTraceGoodSetProjective
open BinaryFrattiniFullFiberInduction
variable (F : Type) [Field F] [Finite F]

theorem centralBase (hodd : Odd (Nat.card F)) (hsize : 3 < Nat.card F)
    (h3 : (3 : F) ≠ 0) (hgood : IsGeneratingGoodSet (goodSet (F := F))) :
    CentralBase (Q F) (projectiveGoodSet (F := F)) := by
  let : Group.IsPerfect (SLTwo.SL2 F) :=
    OddPSLTwoCentralObstruction.reference_isPerfect F hsize
  exact CentralReferenceGoodSet.centralBase (OddPSLTwoCentralKernel.kernelBound F hodd)
    (quotient F) (QuotientGroup.mk'_surjective _)
    (by change (QuotientGroup.mk' (Subgroup.center (SLTwo.SL2 F))).ker ≤ _; simp)
    (OddSLTwoCenter.card_ker_quotient F hodd) _
    (SLTwoTraceGoodSetProjective.hasOddGeneratingGoodSetOver h3 hgood)

theorem minimalNonabelianLift (hodd : Odd (Nat.card F)) (hsize : 17 ≤ Nat.card F)
    (hpair : ∀ c ∈ projectiveGoodSet (F := F), ∃ α β : Q F,
      Subgroup.closure ({α, β} : Set (Q F)) = ⊤ ∧
      ∃ m n : ℕ, IsConj α (c ^ m) ∧ IsConj β (c ^ n)) :
    MinimalNonabelianLift (Q F) (projectiveGoodSet (F := F)) := by
  let : Fintype F := Fintype.ofFinite F
  intro A _ _ _ π _ hπ hR hRΦ N _ hNR hmin hnonabelian Y hY hsub
  apply hY.preimage_quotient_of_full_fiber N (hNR.trans hRΦ)
  intro a b hgen hc t
  let e := QuotientGroup.quotientKerEquivOfSurjective π hπ
  have himage : e (QuotientGroup.mk' π.ker (paperCommutator a b)) ∈
      projectiveGoodSet (F := F) := hsub hc
  have hne : QuotientGroup.mk' π.ker (paperCommutator a b) ≠ 1 := by
    intro hz
    exact (one_not_mem (F := F)) (by simpa only [hz, map_one] using himage)
  obtain ⟨α, β, hgenPair, m, n, hα, hβ⟩ := hpair _ himage
  exact exists_paperCommutator_mul_eq_of_minimal_odd_pslTwo_generating_powers
    F N (hR.to_le hNR) hmin hnonabelian π.ker hR hRΦ e
    (by simpa only [Nat.card_eq_fintype_card] using hodd)
    (by simpa only [Nat.card_eq_fintype_card] using hsize)
    a b hgen hne α β hgenPair m n hα hβ t

theorem hasOddGeneratingGoodSetOver (hodd : Odd (Nat.card F)) (hsize : 17 ≤ Nat.card F)
    (h3 : (3 : F) ≠ 0) (hgood : IsGeneratingGoodSet (goodSet (F := F)))
    (hpair : ∀ c ∈ projectiveGoodSet (F := F), ∃ α β : Q F,
      Subgroup.closure ({α, β} : Set (Q F)) = ⊤ ∧
      ∃ m n : ℕ, IsConj α (c ^ m) ∧ IsConj β (c ^ n))
    {G : Type} [Group G] [Finite G] [Group.IsPerfect G]
    (π : G →* Q F) (hπ : Function.Surjective π)
    (hR : IsPGroup 2 π.ker) (hRΦ : π.ker ≤ frattini G) :
    HasOddGeneratingGoodSetOver π (projectiveGoodSet (F := F)) := by
  let : IsSimpleGroup (Q F) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
  exact BinaryFrattiniFullFiberInduction.hasOddGeneratingGoodSetOver (Q F)
    (projectiveGoodSet (F := F)) (centralBase F hodd (by omega) h3 hgood)
    (minimalNonabelianLift F hodd hsize hpair) π hπ hR hRΦ

end Kourovka2135.OddPSLTwoTraceFrattini
