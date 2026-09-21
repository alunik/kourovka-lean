import Kourovka2135.OddGeneratingGoodSet
import Kourovka2135.MinimalNoncentral
import Mathlib.GroupTheory.PGroup

/-! Binary Frattini induction with two explicit family inputs.

The central case supplies an actual generating good set containing an odd
element. The minimal nonabelian case supplies goodness of the whole inverse
image of any allowed quotient good set. The abelian case and preservation
of the odd element are proved here from the existing checked lifting lemmas.
Neither family input is asserted by this structural assembly. No hypothesis
that the allowed set excludes one is needed in the assembly itself.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.BinaryFrattiniFullFiberInduction

variable (Q : Type) [Group Q] (B : Set Q)

/-- The explicit central-cover base case, without a Frattini restriction. -/
def CentralBase : Prop :=
  ∀ (A : Type) [Group A] [Finite A] [Group.IsPerfect A]
    (pi : A →* Q), Function.Surjective pi → IsPGroup 2 pi.ker →
      pi.ker ≤ Subgroup.center A → HasOddGeneratingGoodSetOver pi B

/-- The explicit full-preimage input for a minimal nonabelian subgroup of
the binary Frattini kernel. The actual simple quotient instance is available
to applications of their minimal-kernel fiber theorem. -/
def MinimalNonabelianLift : Prop :=
  ∀ (A : Type) [Group A] [Finite A] [Group.IsPerfect A]
    (pi : A →* Q) [IsSimpleGroup (A ⧸ pi.ker)],
    Function.Surjective pi → IsPGroup 2 pi.ker → pi.ker ≤ frattini A →
    ∀ (N : Subgroup A) [N.Normal] (hNR : N ≤ pi.ker),
      (∀ L : Subgroup A, L.Normal → L < N → L ≤ Subgroup.center A) →
      (¬ IsMulCommutative N) →
      ∀ Y : Set (A ⧸ N), IsGeneratingGoodSet Y →
        Y ⊆ (QuotientGroup.lift N pi hNR) ⁻¹' B →
        IsGeneratingGoodSet ((QuotientGroup.mk' N) ⁻¹' Y)

/-- The two displayed family inputs imply the complete odd-good-set
invariant through every finite perfect binary Frattini cover. -/
theorem hasOddGeneratingGoodSetOver [IsSimpleGroup Q]
    (hcentralBase : CentralBase Q B)
    (hnonabelianLift : MinimalNonabelianLift Q B)
    {G : Type} [Group G] [Finite G] [Group.IsPerfect G]
    (pi : G →* Q) (hpi : Function.Surjective pi)
    (hR : IsPGroup 2 pi.ker) (hRΦ : pi.ker ≤ frattini G) :
    HasOddGeneratingGoodSetOver pi B := by
  classical
  let T : ℕ → Prop := fun n =>
    ∀ (A : Type) [Group A] [Finite A] [Group.IsPerfect A], Nat.card A = n →
      ∀ pi : A →* Q, Function.Surjective pi →
        IsPGroup 2 pi.ker → pi.ker ≤ frattini A → HasOddGeneratingGoodSetOver pi B
  have main : ∀ n, T n := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih A _ _ _ hAcard pi hpi hR hRΦ
    let e := QuotientGroup.quotientKerEquivOfSurjective pi hpi
    let : IsSimpleGroup (A ⧸ pi.ker) := e.isSimpleGroup
    by_cases hcentral : pi.ker ≤ Subgroup.center A
    · exact hcentralBase A pi hpi hR hcentral
    obtain ⟨N, hNR, hnormal, hnc, hmin⟩ :=
      exists_minimal_normal_noncentral pi.ker hcentral
    let : N.Normal := hnormal
    let qN := QuotientGroup.mk' N
    let pi' := QuotientGroup.lift N pi hNR
    have hqN : Function.Surjective qN := QuotientGroup.mk'_surjective N
    have hpi' : Function.Surjective pi' :=
      QuotientGroup.lift_surjective_of_surjective N pi hpi hNR
    have hker : pi'.ker = pi.ker.map qN := QuotientGroup.ker_lift N pi hNR
    have hR' : IsPGroup 2 pi'.ker := by
      rw [hker]
      exact hR.map qN
    have hΦ' : pi'.ker ≤ frattini (A ⧸ N) := by
      rw [hker]
      exact Subgroup.map_le_iff_le_comap.mpr
        (hRΦ.trans (frattini_le_comap_frattini_of_surjective hqN))
    have hNne : N ≠ ⊥ := fun h => hnc (h ▸ bot_le)
    have hlt : Nat.card (A ⧸ N) < n := by
      rw [← hAcard]
      have hn : 1 < Nat.card N := (Subgroup.one_lt_card_iff_ne_bot N).mpr hNne
      have hpos : 0 < Nat.card (A ⧸ N) := Nat.card_pos
      have hc := Subgroup.card_eq_card_quotient_mul_card_subgroup (α := A) (s := N)
      nlinarith
    have hi := ih (Nat.card (A ⧸ N)) hlt (A ⧸ N) rfl pi' hpi' hR' hΦ'
    apply hi.lift qN hqN
    intro Y hY hYsub
    by_cases hab : IsMulCommutative N
    · let : IsMulCommutative N := hab
      exact hY.preimage_quotient_of_abelian N (hNR.trans hRΦ)
        (commutator_eq_self_of_minimal_noncentral N hnc hmin)
    · exact hnonabelianLift A pi hpi hR hRΦ N hNR hmin hab Y hY hYsub
  exact main (Nat.card G) G rfl pi hpi hR hRΦ

end Kourovka2135.BinaryFrattiniFullFiberInduction
