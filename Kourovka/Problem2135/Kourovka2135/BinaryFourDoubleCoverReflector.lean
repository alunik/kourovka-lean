import Kourovka2135.A5ReflectorCorrection
import Kourovka2135.NormalizerCoprimeKernelLift
import Kourovka2135.SLTwoFiveReflectorData
import Kourovka2135.MinimalBinaryFourAbelian
import Kourovka2135.BinaryFourAlternatingEquiv
import Kourovka2135.CoprimePGroupLift

/-! The persistent reflector through the entire moving kernel of a binary
Frattini cover. Its two inputs retain their exact images in SL2(F5), and its
commutator inverts the chosen order-three element. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
noncomputable section

namespace Kourovka2135.BinaryFourDoubleCoverReflector

open scoped IsMulCommutative

abbrev E := SLTwoFiveAlternating.S

variable {F : Type} [Field F] [Fintype F] [CharP F 2]
variable [IsSimpleGroup (SLTwo.SL2 F)]

/-- The actual reflector lifts with both prescribed persistent input images. -/
theorem exists_inputs_inverting
    (hcard : Fintype.card F = 4)
    {G : Type} [Group G] [Finite G] [Group.IsPerfect G]
    (f : G →* E) (hf : Function.Surjective f)
    (hR : IsPGroup 2 (SLTwoFiveAlternating.toAlternating.comp f).ker)
    (hF : (SLTwoFiveAlternating.toAlternating.comp f).ker ≤ frattini G)
    (hmove : ⁅f.ker, (⊤ : Subgroup G)⁆ = f.ker)
    (u : G) (hu : orderOf u = 3) (hfu : f u = SLTwoFiveReflectorData.uE) :
    ∃ b c : G, f b = SLTwoFiveReflectorData.b ∧ f c = SLTwoFiveReflectorData.c ∧
      (paperCommutator b c)⁻¹ * u * paperCommutator b c = u⁻¹ := by
  classical
  let T : ℕ → Prop := fun n =>
    ∀ (A : Type) [Group A] [Finite A] [Group.IsPerfect A], Nat.card A = n →
      ∀ f : A →* E, Function.Surjective f →
        IsPGroup 2 (SLTwoFiveAlternating.toAlternating.comp f).ker →
        (SLTwoFiveAlternating.toAlternating.comp f).ker ≤ frattini A →
        ⁅f.ker, (⊤ : Subgroup A)⁆ = f.ker →
        ∀ u : A, orderOf u = 3 → f u = SLTwoFiveReflectorData.uE →
          ∃ b c : A, f b = SLTwoFiveReflectorData.b ∧ f c = SLTwoFiveReflectorData.c ∧
            (paperCommutator b c)⁻¹ * u * paperCommutator b c = u⁻¹
  have main : ∀ n, T n := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih A _ _ _ hAcard f hf hR hF hm u hu hfu
    by_cases hcentral : f.ker ≤ Subgroup.center A
    · have hb : f.ker = ⊥ := hm.symm.trans
        (Subgroup.commutator_top_right_eq_bot_iff_le_center.mpr hcentral)
      have hinj := (MonoidHom.ker_eq_bot_iff f).mp hb
      obtain ⟨b, hb⟩ := hf SLTwoFiveReflectorData.b
      obtain ⟨c, hc⟩ := hf SLTwoFiveReflectorData.c
      refine ⟨b, c, hb, hc, hinj ?_⟩
      have hab : f (paperCommutator b c) = SLTwoFiveReflectorData.a := by
        rw [map_paperCommutator, hb, hc, ← SLTwoFiveReflectorData.a_eq_commutator]
      simpa only [map_mul, map_inv, hab, hfu] using
        SLTwoFiveReflectorData.a_inv_conjugates_uE
    · let pi := SLTwoFiveAlternating.toAlternating.comp f
      have hpi : Function.Surjective pi := SLTwoFiveAlternating.toAlternating_surjective.comp hf
      have hk : f.ker ≤ pi.ker := by
        intro x hx
        change SLTwoFiveAlternating.toAlternating (f x) = 1
        rw [show f x = 1 from hx, map_one]
      obtain ⟨N, hNf, hnormal, hnc, hmin⟩ := exists_minimal_normal_noncentral f.ker hcentral
      let : N.Normal := hnormal
      have hNR : N ≤ pi.ker := hNf.trans hk
      have hN : IsPGroup 2 N := hR.to_le hNR
      let e := (BinaryFourAlternatingEquiv.equiv hcard).trans
        (QuotientGroup.quotientKerEquivOfSurjective pi hpi).symm
      let : IsSimpleGroup (A ⧸ pi.ker) := e.symm.isSimpleGroup
      let : IsMulCommutative N :=
        minimal_binary_four_isMulCommutative N hN hmin pi.ker hR hNR hF e hcard
      let q := QuotientGroup.mk' N
      let f' := QuotientGroup.lift N f hNf
      have hq : Function.Surjective q := QuotientGroup.mk'_surjective N
      have hfs : Function.Surjective f' :=
        QuotientGroup.lift_surjective_of_surjective N f hf hNf
      have hfk : f'.ker = f.ker.map q := QuotientGroup.ker_lift N f hNf
      have hpmap : SLTwoFiveAlternating.toAlternating.comp f' =
          QuotientGroup.lift N pi hNR := by
        apply MonoidHom.ext
        intro x
        obtain ⟨a, rfl⟩ := hq x
        rfl
      have hpk : (SLTwoFiveAlternating.toAlternating.comp f').ker = pi.ker.map q := by
        rw [hpmap]
        exact QuotientGroup.ker_lift N pi hNR
      have hRp : IsPGroup 2 (SLTwoFiveAlternating.toAlternating.comp f').ker := by
        rw [hpk]
        exact hR.map q
      have hFp : (SLTwoFiveAlternating.toAlternating.comp f').ker ≤ frattini (A ⧸ N) := by
        rw [hpk]
        exact Subgroup.map_le_iff_le_comap.mpr
          (hF.trans (frattini_le_comap_frattini_of_surjective hq))
      have hmp : ⁅f'.ker, (⊤ : Subgroup (A ⧸ N))⁆ = f'.ker := by
        rw [hfk, ← Subgroup.map_top_of_surjective q hq, ← Subgroup.map_commutator, hm]
      have hNne : N ≠ ⊥ := fun h => hnc (h ▸ bot_le)
      have hlt : Nat.card (A ⧸ N) < n := by
        rw [← hAcard]
        have hn : 1 < Nat.card N := (Subgroup.one_lt_card_iff_ne_bot N).mpr hNne
        have hpos : 0 < Nat.card (A ⧸ N) := Nat.card_pos
        have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup (α := A) (s := N)
        nlinarith
      have hqu : orderOf (q u) = 3 := by
        rw [orderOf_quotient_eq_of_coprime_pgroup Nat.prime_two N hN u]
        · exact hu
        · rw [hu]
          decide
      obtain ⟨b', c', hb', hc', hi⟩ := ih (Nat.card (A ⧸ N)) hlt (A ⧸ N) rfl
        f' hfs hRp hFp hmp (q u) hqu hfu
      obtain ⟨b, hb⟩ := hq b'
      obtain ⟨c, hc⟩ := hq c'
      have hfb : f b = SLTwoFiveReflectorData.b := by
        change f' (q b) = _
        rw [hb]
        exact hb'
      have hfc : f c = SLTwoFiveReflectorData.c := by
        change f' (q c) = _
        rw [hc]
        exact hc'
      have hqN : IsPGroup 2 q.ker := by
        rw [QuotientGroup.ker_mk']
        exact hN
      obtain ⟨a, hqa, ha⟩ := NormalizerCoprimeKernelLift.exists_lift_inverting_order_three
        q hq hqN u hu (paperCommutator b' c') hi
      have hcoset : (paperCommutator b c)⁻¹ * a ∈ N := by
        apply (QuotientGroup.eq_one_iff _).mp
        change q ((paperCommutator b c)⁻¹ * a) = 1
        simp only [paperCommutator, map_mul, map_inv, hb, hc, hqa, inv_mul_cancel]
      have hpu : pi u = A5RelativeModuleCertificate.u := by
        change SLTwoFiveAlternating.toAlternating (f u) = _
        rw [hfu, SLTwoFiveReflectorData.toAlternating_uE]
      have hpc : pi c = A5RelativeModuleCertificate.w := by
        change SLTwoFiveAlternating.toAlternating (f c) = _
        rw [hfc, SLTwoFiveReflectorData.toAlternating_c]
      obtain ⟨x, y, hxy⟩ := A5ReflectorCorrection.exists_corrections_inverting
        N hN hnc hmin pi hpi hR hF u b c a hpu hpc ha hcoset
      refine ⟨b * x, c * y, ?_, ?_, hxy⟩
      · rw [map_mul, show f (x : A) = 1 from hNf x.property, mul_one]
        exact hfb
      · rw [map_mul, show f (y : A) = 1 from hNf y.property, mul_one]
        exact hfc
  exact main (Nat.card G) G rfl f hf hR hF hmove u hu hfu

end Kourovka2135.BinaryFourDoubleCoverReflector
