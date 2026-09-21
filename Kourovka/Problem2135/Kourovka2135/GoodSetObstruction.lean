import Kourovka2135.CoprimeFiber
import Kourovka2135.MinimalDerivedVanishing

/-! Complete good fibers containing a nontrivial prime-to-p quotient element exclude a minimal exception. -/

set_option autoImplicit false
universe u v
namespace Kourovka2135
variable {G : Type u} [Group G] [Finite G] {H : Type v} [Group H]
variable {w : OuterWord} {p : ℕ}

theorem OrderMinimalException.no_good_preimage_with_coprime_element
    (h : OrderMinimalException w p G) (hp : p.Prime)
    (hnoncentral : ¬ solubleRadical G ≤ Subgroup.center G)
    (f : G →* H) (hf : Function.Surjective f)
    {Y : Set H} (hY : IsGeneratingGoodSet (f ⁻¹' Y))
    {y : H} (hy : y ∈ Y) (hne : y ≠ 1) (hyp : ¬ p ∣ orderOf y) : False := by
  obtain ⟨x, hx, hxne, hxp⟩ := exists_nontrivial_coprime_value_of_good_preimage
    hp f hf hY hy hne hyp (OuterWord.derivedWord w.height)
  exact hxne (h.derivedValue_eq_one_of_coprime hp hnoncentral le_rfl hx hxp)

end Kourovka2135
