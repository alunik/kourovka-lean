import Kourovka2135.PerfectVerbal
import Mathlib.Data.Set.Finite.Lemmas

/-! Minimal normal noncentral kernels in a perfect group satisfy [N,G] = N. -/

set_option autoImplicit false
universe u
namespace Kourovka2135
variable {G : Type u} [Group G]

theorem le_center_of_commutator_le_center [Group.IsPerfect G]
    (N : Subgroup G) (h : ⁅N, (⊤ : Subgroup G)⁆ ≤ Subgroup.center G) :
    N ≤ Subgroup.center G := by
  let q := QuotientGroup.mk' (Subgroup.center G)
  have hmapbot : (⁅N, (⊤ : Subgroup G)⁆).map q = ⊥ := by
    apply (Subgroup.map_eq_bot_iff _).mpr
    simpa only [q, QuotientGroup.ker_mk'] using h
  have htop : (⊤ : Subgroup G).map q = ⊤ := by
    rw [← MonoidHom.range_eq_map]
    exact MonoidHom.range_eq_top_of_surjective q (QuotientGroup.mk'_surjective _)
  rw [Subgroup.map_commutator, htop, Subgroup.commutator_top_right_eq_bot_iff_le_center,
    Group.IsPerfect.center_quotient_center_eq_bot] at hmapbot
  have hmap : N.map q = ⊥ := bot_unique hmapbot
  simpa only [q, QuotientGroup.ker_mk'] using (N.map_eq_bot_iff.mp hmap)

theorem commutator_eq_self_of_minimal_noncentral [Group.IsPerfect G]
    (N : Subgroup G) [N.Normal] (hnoncentral : ¬ N ≤ Subgroup.center G)
    (hmin : ∀ M : Subgroup G, M.Normal → M < N → M ≤ Subgroup.center G) :
    ⁅N, (⊤ : Subgroup G)⁆ = N := by
  have hle : ⁅N, (⊤ : Subgroup G)⁆ ≤ N := Subgroup.commutator_le_left _ _
  by_contra hne
  have hcentral := hmin _ inferInstance (lt_of_le_of_ne hle hne)
  exact hnoncentral (le_center_of_commutator_le_center N hcentral)

theorem exists_minimal_normal_noncentral [Finite G]
    (R : Subgroup G) [R.Normal] (hR : ¬ R ≤ Subgroup.center G) :
    ∃ N : Subgroup G, N ≤ R ∧ N.Normal ∧ ¬ N ≤ Subgroup.center G ∧
      ∀ M : Subgroup G, M.Normal → M < N → M ≤ Subgroup.center G := by
  classical
  let : Finite (Subgroup G) := Finite.of_injective (fun H : Subgroup G => (H : Set G))
    SetLike.coe_injective
  let S : Set (Subgroup G) := {N | N ≤ R ∧ N.Normal ∧ ¬ N ≤ Subgroup.center G}
  obtain ⟨N, hN, hmin⟩ := Set.exists_min_image S (fun N => Nat.card N) (Set.toFinite _)
    ⟨R, le_rfl, inferInstance, hR⟩
  refine ⟨N, hN.1, hN.2.1, hN.2.2, ?_⟩
  intro M hM hlt
  by_contra hn
  have hc := hmin M ⟨hlt.le.trans hN.1, hM, hn⟩
  exact (not_le_of_gt (Subgroup.card_lt_of_lt hlt)) hc

end Kourovka2135
