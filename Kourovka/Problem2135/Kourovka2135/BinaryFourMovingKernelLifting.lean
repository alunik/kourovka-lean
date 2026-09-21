import Kourovka2135.MinimalBinaryFourAbelian
import Kourovka2135.GoodSetEquiv
import Kourovka2135.PerfectMovingKernel

/-! Actual generating-good sets lift through every moving Frattini kernel
inside a binary radical with four-parameter SL2 quotient. The induction uses
the proved abelianness of each minimal noncentral kernel. -/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.BinaryFourMovingKernelLifting

open scoped IsMulCommutative

variable {F : Type} [Field F] [Fintype F] [CharP F 2]
variable [IsSimpleGroup (SLTwo.SL2 F)]
variable {Q : Type} [Group Q]

/-- The entire inverse image is generating-good, including even-order fibers. -/
theorem preimage
    (hcard : Fintype.card F = 4)
    {G : Type} [Group G] [Finite G] [Group.IsPerfect G]
    (pi : G →* SLTwo.SL2 F) (hpi : Function.Surjective pi)
    (hR : IsPGroup 2 pi.ker) (hF : pi.ker ≤ frattini G)
    (f : G →* Q) (hf : Function.Surjective f) (hker : f.ker ≤ pi.ker)
    (hmove : ⁅f.ker, (⊤ : Subgroup G)⁆ = f.ker)
    {Y : Set Q} (hY : IsGeneratingGoodSet Y) : IsGeneratingGoodSet (f ⁻¹' Y) := by
  classical
  let T : ℕ → Prop := fun n =>
    ∀ (A : Type) [Group A] [Finite A] [Group.IsPerfect A], Nat.card A = n →
      ∀ pi : A →* SLTwo.SL2 F, Function.Surjective pi →
        IsPGroup 2 pi.ker → pi.ker ≤ frattini A →
        ∀ f : A →* Q, Function.Surjective f → f.ker ≤ pi.ker →
          ⁅f.ker, (⊤ : Subgroup A)⁆ = f.ker → IsGeneratingGoodSet (f ⁻¹' Y)
  have main : ∀ n, T n := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih A _ _ _ hAcard pi hpi hR hF f hf hker hm
    by_cases hc : f.ker ≤ Subgroup.center A
    · have hb : f.ker = ⊥ := hm.symm.trans
        (Subgroup.commutator_top_right_eq_bot_iff_le_center.mpr hc)
      exact hY.preimage_of_bijective f ⟨(MonoidHom.ker_eq_bot_iff f).mp hb, hf⟩
    · obtain ⟨N, hNf, hnormal, hnc, hmin⟩ := exists_minimal_normal_noncentral f.ker hc
      let : N.Normal := hnormal
      have hNR : N ≤ pi.ker := hNf.trans hker
      let e := QuotientGroup.quotientKerEquivOfSurjective pi hpi
      let : IsSimpleGroup (A ⧸ pi.ker) := e.isSimpleGroup
      let : IsMulCommutative N := minimal_binary_four_isMulCommutative N
        (hR.to_le hNR) hmin pi.ker hR hNR hF e.symm hcard
      let q := QuotientGroup.mk' N
      let pi' := QuotientGroup.lift N pi hNR
      let f' := QuotientGroup.lift N f hNf
      have hq : Function.Surjective q := QuotientGroup.mk'_surjective N
      have hpis : Function.Surjective pi' :=
        QuotientGroup.lift_surjective_of_surjective N pi hpi hNR
      have hfs : Function.Surjective f' :=
        QuotientGroup.lift_surjective_of_surjective N f hf hNf
      have hpk : pi'.ker = pi.ker.map q := QuotientGroup.ker_lift N pi hNR
      have hfk : f'.ker = f.ker.map q := QuotientGroup.ker_lift N f hNf
      have hRp : IsPGroup 2 pi'.ker := by rw [hpk]; exact hR.map q
      have hFp : pi'.ker ≤ frattini (A ⧸ N) := by
        rw [hpk]
        exact Subgroup.map_le_iff_le_comap.mpr
          (hF.trans (frattini_le_comap_frattini_of_surjective hq))
      have hk : f'.ker ≤ pi'.ker := by
        rw [hfk, hpk]
        exact Subgroup.map_mono hker
      have hmp : ⁅f'.ker, (⊤ : Subgroup (A ⧸ N))⁆ = f'.ker := by
        rw [hfk, ← Subgroup.map_top_of_surjective q hq, ← Subgroup.map_commutator, hm]
      have hNne : N ≠ ⊥ := fun h => hnc (h ▸ bot_le)
      have hlt : Nat.card (A ⧸ N) < n := by
        rw [← hAcard]
        have hn : 1 < Nat.card N := (Subgroup.one_lt_card_iff_ne_bot N).mpr hNne
        have hpos : 0 < Nat.card (A ⧸ N) := Nat.card_pos
        have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup (α := A) (s := N)
        nlinarith
      have hi := ih (Nat.card (A ⧸ N)) hlt (A ⧸ N) rfl pi' hpis hRp hFp f' hfs hk hmp
      exact hi.preimage_quotient_of_abelian N (hNR.trans hF)
        (commutator_eq_self_of_minimal_noncentral N hnc hmin)
  exact main (Nat.card G) G rfl pi hpi hR hF f hf hker hmove

/-- In particular the canonical central quotient has full persistent fibers. -/
theorem preimage_canonical
    (hcard : Fintype.card F = 4)
    {G : Type} [Group G] [Finite G] [Group.IsPerfect G]
    (pi : G →* SLTwo.SL2 F) (hpi : Function.Surjective pi)
    (hR : IsPGroup 2 pi.ker) (hF : pi.ker ≤ frattini G)
    {Y : Set (G ⧸ ⁅pi.ker, (⊤ : Subgroup G)⁆)} (hY : IsGeneratingGoodSet Y) :
    IsGeneratingGoodSet ((QuotientGroup.mk' ⁅pi.ker, (⊤ : Subgroup G)⁆) ⁻¹' Y) := by
  apply preimage hcard pi hpi hR hF (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  · rw [QuotientGroup.ker_mk']
    exact Subgroup.commutator_le_left _ _
  · rw [QuotientGroup.ker_mk']
    exact commutator_top_idempotent_of_isPerfect pi.ker
  · exact hY

end Kourovka2135.BinaryFourMovingKernelLifting
