import Kourovka2135.PerfectVerbal
import Mathlib.Data.Set.Finite.Lemmas

/-! A subgroup surjecting onto a finite perfect quotient contains a perfect supplement. -/

set_option autoImplicit false
universe u v
namespace Kourovka2135
variable {G : Type u} {Q : Type v} [Group G] [Group Q] [Finite G]

theorem exists_perfect_subgroup_map_top [Group.IsPerfect Q]
    (f : G →* Q) (H : Subgroup G) (hH : H.map f = ⊤) :
    ∃ K : Subgroup G, K ≤ H ∧ K.map f = ⊤ ∧ Group.IsPerfect K := by
  let : Finite (Subgroup G) := Finite.of_injective (fun H : Subgroup G => (H : Set G))
    SetLike.coe_injective
  let S : Set (Subgroup G) := {K | K ≤ H ∧ K.map f = ⊤}
  obtain ⟨K, hK, hmin⟩ := Set.exists_min_image S (fun K => Nat.card K)
    (Set.toFinite _) ⟨H, le_rfl, hH⟩
  refine ⟨K, hK.1, hK.2, Subgroup.isPerfect_iff.mpr ?_⟩
  have hDle : ⁅K, K⁆ ≤ K := Subgroup.commutator_le.mpr fun a ha b hb =>
    K.mul_mem (K.mul_mem (K.mul_mem ha hb) (K.inv_mem ha)) (K.inv_mem hb)
  have hDmap : (⁅K, K⁆).map f = ⊤ := by
    rw [Subgroup.map_commutator, hK.2]
    exact Group.IsPerfect.commutator_eq_top
  by_contra hne
  have hlt : Nat.card (⁅K, K⁆ : Subgroup G) < Nat.card K :=
    Subgroup.card_lt_of_lt (lt_of_le_of_ne hDle hne)
  exact (not_le_of_gt hlt) (hmin _ ⟨hDle.trans hK.1, hDmap⟩)

omit [Finite G] in
theorem map_quotient_eq_top_iff_sup (N : Subgroup G) [N.Normal] (H : Subgroup G) :
    H.map (QuotientGroup.mk' N) = ⊤ ↔ H ⊔ N = ⊤ := by
  constructor
  · intro heq
    have hc := congrArg (Subgroup.comap (QuotientGroup.mk' N)) heq
    simpa only [Subgroup.comap_map_eq, QuotientGroup.ker_mk', Subgroup.comap_top] using hc
  · intro heq
    apply Subgroup.comap_injective (QuotientGroup.mk'_surjective N)
    simpa only [Subgroup.comap_map_eq, QuotientGroup.ker_mk', Subgroup.comap_top] using heq

theorem exists_perfect_supplement (N : Subgroup G) [N.Normal]
    [Group.IsPerfect (G ⧸ N)] (H : Subgroup G) (hH : H ⊔ N = ⊤) :
    ∃ K : Subgroup G, K ≤ H ∧ K ⊔ N = ⊤ ∧ Group.IsPerfect K := by
  obtain ⟨K, hKH, hK, hperfect⟩ := exists_perfect_subgroup_map_top
    (QuotientGroup.mk' N) H ((map_quotient_eq_top_iff_sup N H).mpr hH)
  exact ⟨K, hKH, (map_quotient_eq_top_iff_sup N K).mp hK, hperfect⟩

end Kourovka2135
