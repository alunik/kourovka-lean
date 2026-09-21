import Kourovka2135.CentralDoubleCoverUniqueness
import Kourovka2135.Statement

/-! A central binary cover is the base or the actual reference double cover.
The product-order condition is also transported across an actual equivalence. -/

set_option autoImplicit false
noncomputable section
namespace Kourovka2135
universe u v

theorem ProductOrderCondition.of_injective
    {G : Type u} {H : Type v} [Group G] [Group H] {w : OuterWord} {p : ℕ}
    (h : ProductOrderCondition w p H) (f : G →* H) (hf : Function.Injective f) :
    ProductOrderCondition w p G := by
  intro x hx y hy hxp hyp
  have hox := orderOf_injective f hf x
  have hoy := orderOf_injective f hf y
  have hoxy := orderOf_injective f hf (x * y)
  have hh := h (f x) (w.map_mem_values f hx) (f y) (w.map_mem_values f hy)
    (by simpa only [hox] using hxp) (by simpa only [hoy] using hyp)
  simpa only [← map_mul, hoxy] using hh

namespace CentralDoubleCoverUniqueness

theorem exists_equiv_reference_or_base
    {Q E G : Type u} [Group Q] [Group E] [Group G]
    [Finite E] [Group.IsPerfect E] [Finite G] [Group.IsPerfect G]
    (hbound : KernelBound Q) (π₀ : E →* Q) (hπ₀ : Function.Surjective π₀)
    (hc₀ : π₀.ker ≤ Subgroup.center E) (hcard₀ : Nat.card π₀.ker = 2)
    (π : G →* Q) (hπ : Function.Surjective π)
    (hbinary : IsPGroup 2 π.ker) (hc : π.ker ≤ Subgroup.center G) :
    Nonempty (G ≃* E) ∨ Nonempty (G ≃* Q) := by
  by_cases hbot : π.ker = ⊥
  · exact Or.inr ⟨MulEquiv.ofBijective π ⟨(MonoidHom.ker_eq_bot_iff π).mp hbot, hπ⟩⟩
  · have hb := hbound G π hπ hc hbinary
    have hcard : Nat.card π.ker = 2 := by
      have hpos := (Subgroup.one_lt_card_iff_ne_bot π.ker).mpr hbot
      omega
    obtain ⟨e, _⟩ := exists_equiv_over hbound π π₀ hπ hπ₀ hc hc₀ hcard hcard₀
    exact Or.inl ⟨e⟩

end CentralDoubleCoverUniqueness
end Kourovka2135
