import Mathlib.GroupTheory.Sylow

/-! Actual prime-power subgroup lifts through finite surjections.

A Sylow subgroup of the full inverse image maps onto the prescribed
prime-power subgroup. No splitting or coprime-kernel hypothesis is required.
-/

set_option autoImplicit false
noncomputable section
universe u v
namespace Kourovka2135.PGroupSubgroupLift

variable {G : Type u} {H : Type v} [Group G] [Group H] [Finite G]

/-- Every q-subgroup in the target of a finite surjection is the exact image
of an actual q-subgroup of the source. -/
theorem exists_subgroup_map_eq {q : ℕ} [Fact q.Prime]
    (f : G →* H) (hf : Function.Surjective f)
    (U : Subgroup H) (hU : IsPGroup q U) :
    ∃ P : Subgroup G, IsPGroup q P ∧ P.map f = U := by
  let L := U.comap f
  let α : L →* U := f.subgroupComap U
  have hα : Function.Surjective α :=
    f.subgroupComap_surjective_of_surjective U hf
  let T : Sylow q L := Classical.choice inferInstance
  let V : Sylow q U := T.mapSurjective hα
  have htop : (V : Subgroup U) = ⊤ := by
    exact (V.is_maximal' (hU.to_subgroup ⊤) le_top).symm
  let P : Subgroup G := (T : Subgroup L).map L.subtype
  refine ⟨P, T.isPGroup'.map L.subtype, ?_⟩
  have hcomp : f.comp L.subtype = U.subtype.comp α := rfl
  calc
    P.map f = ((T : Subgroup L).map α).map U.subtype := by
      change ((T : Subgroup L).map L.subtype).map f = _
      rw [Subgroup.map_map, hcomp, ← Subgroup.map_map]
    _ = (⊤ : Subgroup U).map U.subtype := by
      change (V : Subgroup U).map U.subtype = _
      rw [htop]
    _ = U := by
      apply le_antisymm
      · rintro x ⟨a, _, rfl⟩
        exact a.property
      · intro x hx
        exact ⟨⟨x, hx⟩, Subgroup.mem_top _, rfl⟩

end Kourovka2135.PGroupSubgroupLift
