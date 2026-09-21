import Kourovka2135.GoodSetLifting

/-! Generating good sets descend through epimorphisms. -/

set_option autoImplicit false
universe u v
namespace Kourovka2135
variable {G : Type u} {H : Type v} [Group G] [Group H]

theorem IsGeneratingGoodSet.image_of_surjective (f : G →* H)
    (hf : Function.Surjective f) {X : Set G} (hX : IsGeneratingGoodSet X) :
    IsGeneratingGoodSet (f '' X) := by
  rintro t ⟨x, hx, rfl⟩
  obtain ⟨a, ha, b, hb, hab, hgen⟩ := hX x hx
  refine ⟨f a, ⟨a, ha, rfl⟩, f b, ⟨b, hb, rfl⟩, ?_, ?_⟩
  · simpa only [paperCommutator, map_mul, map_inv] using congrArg f hab
  · rw [← Set.image_pair, ← MonoidHom.map_closure, hgen]
    exact Subgroup.map_top_of_surjective f hf

end Kourovka2135
