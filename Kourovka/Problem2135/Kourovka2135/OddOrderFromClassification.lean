import Kourovka2135.MinimalSimpleEven
import Mathlib.GroupTheory.Index
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.Linarith

/-! Odd-order solubility derived from the explicit minimal-simple classification.
The classification remains a theorem parameter, not a declared axiom. -/

set_option autoImplicit false
universe u
namespace Kourovka2135
open scoped IsMulCommutative

theorem isSolvable_of_odd_card_of_minimalSimpleClassification
    (classification : MinimalSimpleClassification.{u})
    (G : Type u) [Group G] [Finite G]
    (hodd : Odd (Nat.card G)) : Group.IsSolvable G := by
  classical
  induction hn : Nat.card G using Nat.strong_induction_on generalizing G with
  | h n ih =>
    by_contra hsolv
    let : Nontrivial G := by
      rcases subsingleton_or_nontrivial G with hs | hs
      · let : Subsingleton G := hs
        exact (hsolv inferInstance).elim
      · exact hs
    have hproper (H : Subgroup G) (hne : H ≠ ⊤) : Group.IsSolvable H := by
      have hlt : Nat.card H < Nat.card G := by
        simpa only [Subgroup.card_top] using
          (Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hne))
      exact ih (Nat.card H) (hn ▸ hlt) H
        (hodd.of_dvd_nat H.card_subgroup_dvd_card) rfl
    let : IsSimpleGroup G := by
      refine ⟨?_⟩
      intro N hN
      let : N.Normal := hN
      by_cases hbot : N = ⊥
      · exact Or.inl hbot
      by_cases htop : N = ⊤
      · exact Or.inr htop
      have hNc : 1 < Nat.card N := N.one_lt_card_iff_ne_bot.mpr hbot
      have hQpos : 0 < Nat.card (G ⧸ N) := Nat.card_pos
      have hmul := N.index_mul_card
      rw [N.index_eq_card] at hmul
      have hQlt : Nat.card (G ⧸ N) < Nat.card G := by nlinarith
      have hQodd : Odd (Nat.card (G ⧸ N)) := hodd.of_dvd_nat
        (Subgroup.card_dvd_of_surjective (QuotientGroup.mk' N)
          (QuotientGroup.mk'_surjective N))
      have hQsolv : Group.IsSolvable (G ⧸ N) :=
        ih (Nat.card (G ⧸ N)) (hn ▸ hQlt) (G ⧸ N) hQodd rfl
      exact (hsolv ((Group.isSolvable_iff_subgroup_quotient N).mpr
        ⟨hproper N htop, hQsolv⟩)).elim
    have hnonabelian : ¬ IsMulCommutative G := by
      intro hc
      let : IsMulCommutative G := hc
      exact hsolv inferInstance
    exact hodd.not_two_dvd_nat (classification G hnonabelian hproper).two_dvd_card

end Kourovka2135
