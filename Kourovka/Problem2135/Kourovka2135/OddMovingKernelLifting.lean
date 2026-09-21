import Kourovka2135.OddGoodSetLifting
import Kourovka2135.GoodSetEquiv

/-!
Complete good-set lifting through an odd-prime Frattini kernel R satisfying
[R,G]=R. This retains the movement hypothesis and does not assert that central
odd-prime covers vanish.
-/

set_option autoImplicit false
universe u v
namespace Kourovka2135
variable {G : Type u} [Group G] [Finite G] [Group.IsPerfect G]
variable {Q : Type v} [Group Q]

theorem IsGeneratingGoodSet.preimage_of_odd_moving_frattini_kernel
    {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (f : G →* Q) (hf : Function.Surjective f)
    (hR : IsPGroup p f.ker) (hFrattini : f.ker ≤ frattini G)
    (hmove : ⁅f.ker, (⊤ : Subgroup G)⁆ = f.ker)
    {Y : Set Q} (hY : IsGeneratingGoodSet Y) : IsGeneratingGoodSet (f ⁻¹' Y) := by
  classical
  let T : ℕ → Prop := fun n =>
    ∀ (A : Type u) [Group A] [Finite A] [Group.IsPerfect A], Nat.card A = n →
      ∀ f : A →* Q, Function.Surjective f → IsPGroup p f.ker → f.ker ≤ frattini A →
        ⁅f.ker, (⊤ : Subgroup A)⁆ = f.ker → IsGeneratingGoodSet (f ⁻¹' Y)
  have main : ∀ n, T n := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih A _ _ _ hcard f hf hR hF hm
    by_cases hc : f.ker ≤ Subgroup.center A
    · have hb : f.ker = ⊥ := hm.symm.trans
        (Subgroup.commutator_top_right_eq_bot_iff_le_center.mpr hc)
      exact hY.preimage_of_bijective f ⟨(MonoidHom.ker_eq_bot_iff f).mp hb, hf⟩
    · obtain ⟨N, hNR, hnormal, hnc, hab, hNm⟩ :=
        exists_abelian_normal_moving_subgroup_of_odd_frattini hp hodd f.ker hR hF hc
      let : N.Normal := hnormal
      let : IsMulCommutative N := hab
      let q := QuotientGroup.mk' N
      let f' := QuotientGroup.lift N f hNR
      have hq : Function.Surjective q := QuotientGroup.mk'_surjective N
      have hfs : Function.Surjective f' := QuotientGroup.lift_surjective_of_surjective N f hf hNR
      have hk : f'.ker = f.ker.map q := QuotientGroup.ker_lift N f hNR
      have hRp : IsPGroup p f'.ker := by rw [hk]; exact hR.map q
      have hFp : f'.ker ≤ frattini (A ⧸ N) := by
        rw [hk]
        apply Subgroup.map_le_iff_le_comap.mpr
        exact hF.trans (frattini_le_comap_frattini_of_surjective hq)
      have hmp : ⁅f'.ker, (⊤ : Subgroup (A ⧸ N))⁆ = f'.ker := by
        rw [hk, ← Subgroup.map_top_of_surjective q hq, ← Subgroup.map_commutator, hm]
      have hNne : N ≠ ⊥ := fun h => hnc (h ▸ bot_le)
      have hlt : Nat.card (A ⧸ N) < n := by
        rw [← hcard]
        have hn : 1 < Nat.card N := (Subgroup.one_lt_card_iff_ne_bot N).mpr hNne
        have hpos : 0 < Nat.card (A ⧸ N) := Nat.card_pos
        have hc := Subgroup.card_eq_card_quotient_mul_card_subgroup (α := A) (s := N)
        nlinarith
      have hi := ih (Nat.card (A ⧸ N)) hlt (A ⧸ N) rfl f' hfs hRp hFp hmp
      exact hi.preimage_quotient_of_abelian N (hNR.trans hF) hNm
  exact main (Nat.card G) G rfl f hf hR hFrattini hmove

end Kourovka2135
