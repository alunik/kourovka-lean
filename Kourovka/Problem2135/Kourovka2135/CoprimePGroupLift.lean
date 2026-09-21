import Kourovka2135.CoprimeFiber
import Kourovka2135.Quotient
import Mathlib.GroupTheory.PGroup

/-! Exact preservation and lifting of prime-to-p orders across a p-group kernel.
This refines coprime element selection without assuming a complement.
-/

set_option autoImplicit false

namespace Kourovka2135

variable {G : Type*} [Group G] [Finite G]

theorem orderOf_quotient_eq_of_coprime_pgroup
    {p : ℕ} (hp : p.Prime) (N : Subgroup G) [N.Normal] (hN : IsPGroup p N)
    (x : G) (hx : Nat.Coprime p (orderOf x)) :
    orderOf (QuotientGroup.mk' N x) = orderOf x := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨e, he⟩ := hN.exists_card_eq
  have hcop : (orderOf x).Coprime (Nat.card N) := by
    rw [he]
    exact hx.symm.pow_right e
  exact Nat.dvd_antisymm (orderOf_map_dvd (QuotientGroup.mk' N) x)
    (hcop.dvd_mul_right.mp (orderOf_dvd_orderOf_quotient_mul_card N x))

theorem exists_order_preserving_lift_of_pgroup
    {p : ℕ} (hp : p.Prime) (N : Subgroup G) [N.Normal] (hN : IsPGroup p N)
    (y : G ⧸ N) (hy : ¬ p ∣ orderOf y) :
    ∃ x : G, QuotientGroup.mk' N x = y ∧ orderOf x = orderOf y := by
  obtain ⟨x, hx, hxp⟩ := exists_coprime_order_lift_of_surjective hp
    (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) y hy
  refine ⟨x, hx, ?_⟩
  rw [← orderOf_quotient_eq_of_coprime_pgroup hp N hN x
    (hp.coprime_iff_not_dvd.mpr hxp), hx]

end Kourovka2135
