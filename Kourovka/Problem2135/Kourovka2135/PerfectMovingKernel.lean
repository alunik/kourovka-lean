import Kourovka2135.MinimalNoncentral

/-! Commuting twice with a perfect ambient group does not shrink a normal subgroup further. -/

set_option autoImplicit false
universe u
namespace Kourovka2135
variable {G : Type u} [Group G] [Group.IsPerfect G]

theorem commutator_top_idempotent_of_isPerfect (R : Subgroup G) [R.Normal] :
    ⁅⁅R, (⊤ : Subgroup G)⁆, (⊤ : Subgroup G)⁆ = ⁅R, (⊤ : Subgroup G)⁆ := by
  let D := ⁅R, (⊤ : Subgroup G)⁆
  let K := ⁅D, (⊤ : Subgroup G)⁆
  let q := QuotientGroup.mk' K
  have hqtop : (⊤ : Subgroup G).map q = ⊤ :=
    Subgroup.map_top_of_surjective q (QuotientGroup.mk'_surjective K)
  have hKbot : K.map q = ⊥ := by
    apply (Subgroup.map_eq_bot_iff K).mpr
    simpa only [q, QuotientGroup.ker_mk'] using (le_refl K)
  have hDc : D.map q ≤ Subgroup.center (G ⧸ K) := by
    apply Subgroup.commutator_top_right_eq_bot_iff_le_center.mp
    rw [← hqtop, ← Subgroup.map_commutator]
    exact hKbot
  have hRc : R.map q ≤ Subgroup.center (G ⧸ K) := by
    apply le_center_of_commutator_le_center
    rw [← hqtop, ← Subgroup.map_commutator]
    exact hDc
  have hDbot : D.map q = ⊥ := by
    change (⁅R, (⊤ : Subgroup G)⁆).map q = ⊥
    rw [Subgroup.map_commutator, hqtop]
    exact Subgroup.commutator_top_right_eq_bot_iff_le_center.mpr hRc
  apply le_antisymm
  · exact Subgroup.commutator_le_left _ _
  · have hle := (D.map_eq_bot_iff).mp hDbot
    simpa only [q, QuotientGroup.ker_mk'] using hle

end Kourovka2135
