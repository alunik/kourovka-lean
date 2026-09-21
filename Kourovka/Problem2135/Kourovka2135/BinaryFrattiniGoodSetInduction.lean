import Kourovka2135.OddGeneratingGoodSet
import Kourovka2135.MinimalBinaryKernelDichotomy
import Kourovka2135.SpecialGoodSetLifting

/-! The complete binary Frattini induction, with its terminal nonspecial
case explicitly exposed. The algebraic dichotomy and the abelian/special
full-fiber lifting steps are proved imports. Instantiating the terminal
input for the actual split-torus set is a separate family theorem.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135

theorem binary_frattini_good_set_induction
    {F : Type} [Field F] [Fintype F] [CharP F 2]
    [IsSimpleGroup (SLTwo.SL2 F)]
    (f : ℕ) (hcard : Fintype.card F = 2 ^ f) (hf : 3 ≤ f)
    (B : Set (SLTwo.SL2 F)) (hB : IsGeneratingGoodSet B)
    (hBne : ∀ s ∈ B, s ≠ 1) (hBodd : ∃ s ∈ B, Odd (orderOf s))
    (hterminal : ∀ (A : Type) [Group A] [Finite A] [Group.IsPerfect A]
      (pi : A →* SLTwo.SL2 F), Function.Surjective pi →
      IsPGroup 2 pi.ker → pi.ker ≤ frattini A →
      (¬ IsMulCommutative pi.ker) →
      Subgroup.center pi.ker ≠ commutator pi.ker →
      (∀ L : Subgroup A, L.Normal → L < pi.ker → L ≤ Subgroup.center A) →
      HasOddGeneratingGoodSetOver pi B)
    {G : Type} [Group G] [Finite G] [Group.IsPerfect G]
    (pi : G →* SLTwo.SL2 F) (hpi : Function.Surjective pi)
    (hR : IsPGroup 2 pi.ker) (hRΦ : pi.ker ≤ frattini G) :
    HasOddGeneratingGoodSetOver pi B := by
  classical
  let T : ℕ → Prop := fun n =>
    ∀ (A : Type) [Group A] [Finite A] [Group.IsPerfect A], Nat.card A = n →
      ∀ pi : A →* SLTwo.SL2 F, Function.Surjective pi →
        IsPGroup 2 pi.ker → pi.ker ≤ frattini A → HasOddGeneratingGoodSetOver pi B
  have main : ∀ n, T n := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih A _ _ _ hAcard pi hpi hR hRΦ
    let e := QuotientGroup.quotientKerEquivOfSurjective pi hpi
    let : IsSimpleGroup (A ⧸ pi.ker) := e.isSimpleGroup
    rcases binary_frattini_kernel_dichotomy pi.ker hR hRΦ e.symm f hcard hf with
      hbot | husable | hlast
    · have hbase : HasOddGeneratingGoodSetOver (MonoidHom.id (SLTwo.SL2 F)) B :=
        ⟨B, hB, fun _ hx => hx, hBodd⟩
      exact hbase.of_equiv (MulEquiv.ofBijective pi
        ⟨(MonoidHom.ker_eq_bot_iff pi).mp hbot, hpi⟩)
    · obtain ⟨N, hNR, hnormal, hnc, hmin, hkind⟩ := husable
      let : N.Normal := hnormal
      let q := QuotientGroup.mk' N
      let pi' := QuotientGroup.lift N pi hNR
      have hq : Function.Surjective q := QuotientGroup.mk'_surjective N
      have hpi' : Function.Surjective pi' :=
        QuotientGroup.lift_surjective_of_surjective N pi hpi hNR
      have hker : pi'.ker = pi.ker.map q := QuotientGroup.ker_lift N pi hNR
      have hR' : IsPGroup 2 pi'.ker := by rw [hker]; exact hR.map q
      have hΦ' : pi'.ker ≤ frattini (A ⧸ N) := by
        rw [hker]
        exact Subgroup.map_le_iff_le_comap.mpr
          (hRΦ.trans (frattini_le_comap_frattini_of_surjective hq))
      have hNne : N ≠ ⊥ := fun h => hnc (h ▸ bot_le)
      have hlt : Nat.card (A ⧸ N) < n := by
        rw [← hAcard]
        have hn : 1 < Nat.card N := (Subgroup.one_lt_card_iff_ne_bot N).mpr hNne
        have hpos : 0 < Nat.card (A ⧸ N) := Nat.card_pos
        have hc := Subgroup.card_eq_card_quotient_mul_card_subgroup (α := A) (s := N)
        nlinarith
      have hi := ih (Nat.card (A ⧸ N)) hlt (A ⧸ N) rfl pi' hpi' hR' hΦ'
      apply hi.lift q hq
      intro Y hY hYsub
      by_cases hab : IsMulCommutative N
      · let : IsMulCommutative N := hab
        exact hY.preimage_quotient_of_abelian N (hNR.trans hRΦ)
          (commutator_eq_self_of_minimal_noncentral N hnc hmin)
      · have hs : Subgroup.center N = commutator N := hkind.resolve_left hab
        have hN : IsPGroup 2 N := hR.to_le hNR
        apply hY.preimage_quotient_of_special_minimal N hN hmin hab hs
          (hNR.trans hRΦ) pi.ker hR
        intro t ht hzero
        have htB : pi t ∈ B := hYsub ht
        apply hBne (pi t) htB
        exact (show t ∈ pi.ker from (QuotientGroup.eq_one_iff _).mp hzero)
    · exact hterminal A pi hpi hR hRΦ hlast.1 hlast.2.1 hlast.2.2
  exact main (Nat.card G) G rfl pi hpi hR hRΦ

end Kourovka2135
