import Kourovka2135.GoodSetImage
import Kourovka2135.ClassTwoCommutators
import Mathlib.GroupTheory.IsPerfect

/-! A nonempty generating-good set proves perfectness directly: its
members are commutators, and two of those members generate the whole group. -/

set_option autoImplicit false

namespace Kourovka2135

theorem IsGeneratingGoodSet.isPerfect {G : Type*} [Group G]
    {Y : Set G} (hY : IsGeneratingGoodSet Y) (hne : Y.Nonempty) :
    Group.IsPerfect G := by
  have hcomm : Y ⊆ commutator G := by
    intro y hy
    obtain ⟨a, _, b, _, hab, _⟩ := hY y hy
    exact hab ▸ paperCommutator_mem_commutator a b
  obtain ⟨y, hy⟩ := hne
  obtain ⟨a, ha, b, hb, _, hgen⟩ := hY y hy
  refine ⟨top_unique ?_⟩
  rw [← hgen]
  apply (Subgroup.closure_le _).mpr
  intro x hx
  rcases Set.mem_insert_iff.mp hx with rfl | hx
  · exact hcomm ha
  · exact Set.mem_singleton_iff.mp hx ▸ hcomm hb

end Kourovka2135
