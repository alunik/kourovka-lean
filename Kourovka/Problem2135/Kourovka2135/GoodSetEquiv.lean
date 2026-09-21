import Kourovka2135.GoodSetLifting

/-! Transport generating good sets along group isomorphisms. -/

set_option autoImplicit false
universe u v
namespace Kourovka2135
variable {G : Type u} {H : Type v} [Group G] [Group H]

theorem IsGeneratingGoodSet.preimage_of_bijective
    (f : G →* H) (hf : Function.Bijective f)
    {Y : Set H} (hY : IsGeneratingGoodSet Y) : IsGeneratingGoodSet (f ⁻¹' Y) := by
  intro t ht
  obtain ⟨a, ha, b, hb, hab, hgen⟩ := hY (f t) ht
  obtain ⟨x, hx⟩ := hf.surjective a
  obtain ⟨y, hy⟩ := hf.surjective b
  refine ⟨x, ?_, y, ?_, ?_, ?_⟩
  · change f x ∈ Y
    rw [hx]
    exact ha
  · change f y ∈ Y
    rw [hy]
    exact hb
  · apply hf.injective
    simpa only [paperCommutator, map_mul, map_inv, hx, hy] using hab
  · apply Subgroup.map_injective hf.injective
    rw [MonoidHom.map_closure, Set.image_pair, hx, hy, hgen,
      Subgroup.map_top_of_surjective f hf.surjective]

end Kourovka2135
