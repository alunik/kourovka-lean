import Kourovka2135.OddGeneratingGoodSet
import Kourovka2135.MinimalDerivedVanishing

/-! The flexible odd-good-set invariant already excludes a binary least
exception with noncentral radical if its allowed images avoid the identity.
It does not require a full good preimage or an even-order quotient witness. -/

set_option autoImplicit false
universe u v
namespace Kourovka2135

theorem OrderMinimalException.no_odd_generating_good_set_over_nontrivial
    {G : Type u} {Q : Type v} [Group G] [Finite G] [Group Q]
    {w : OuterWord} (h : OrderMinimalException w 2 G)
    (hnoncentral : ¬ solubleRadical G ≤ Subgroup.center G)
    (π : G →* Q) (B : Set Q) (hB : 1 ∉ B)
    (hgood : HasOddGeneratingGoodSetOver π B) : False := by
  obtain ⟨x, hx, hxB, hodd⟩ := hgood.exists_value (OuterWord.derivedWord w.height)
  have he := h.derivedValue_eq_one_of_coprime Nat.prime_two hnoncentral le_rfl
    hx hodd.not_two_dvd_nat
  exact hB (by simpa only [he, map_one] using hxB)

end Kourovka2135
