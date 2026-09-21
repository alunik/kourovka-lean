import Kourovka2135.PerfectVerbal
import Mathlib.Data.Set.Finite.Lemmas

/-! A finite group's derived series reaches a perfect term, beyond any requested depth. -/

set_option autoImplicit false
universe u
namespace Kourovka2135
variable {G : Type u} [Group G] [Finite G]

theorem exists_perfect_derivedSeries (n₀ : ℕ) :
    ∃ n : ℕ, n₀ ≤ n ∧ Group.IsPerfect (derivedSeries G n) := by
  let : Finite (Subgroup G) := Finite.of_injective (fun H : Subgroup G => (H : Set G))
    SetLike.coe_injective
  let S : Set (Subgroup G) := {D | ∃ n, n₀ ≤ n ∧ D = derivedSeries G n}
  obtain ⟨D, ⟨n, hn, rfl⟩, hmin⟩ :=
    Set.exists_min_image S (fun D => Nat.card D) (Set.toFinite _)
      ⟨derivedSeries G n₀, n₀, le_rfl, rfl⟩
  refine ⟨n, hn, Subgroup.isPerfect_iff.mpr ?_⟩
  have hle : derivedSeries G (n + 1) ≤ derivedSeries G n :=
    derivedSeries_antitone G (Nat.le_succ n)
  have heq : derivedSeries G (n + 1) = derivedSeries G n := by
    by_contra hne
    have hlt := Subgroup.card_lt_of_lt (lt_of_le_of_ne hle hne)
    exact (not_le_of_gt hlt) (hmin _ ⟨n + 1, hn.trans (Nat.le_succ n), rfl⟩)
  simpa only [derivedSeries_succ] using heq

theorem isSolvable_of_perfect_subgroups_trivial
    (h : ∀ K : Subgroup G, Group.IsPerfect K → K = ⊥) : Group.IsSolvable G := by
  obtain ⟨n, _, hn⟩ := exists_perfect_derivedSeries (G := G) 0
  exact ⟨n, h _ hn⟩

end Kourovka2135
