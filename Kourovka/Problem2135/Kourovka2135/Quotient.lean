import Kourovka2135.Statement

/-!
# Quotients by normal subgroups of coprime order

Element-order divisibility is preserved by a quotient whose kernel has order
coprime to the chosen number. This permits the product-order hypothesis to pass
to these quotients. It does not assert inheritance by arbitrary quotients.
-/

set_option autoImplicit false

universe u

namespace Kourovka2135

variable {G : Type u} [Group G]

/-- Raising to the order of the quotient image puts an element in the kernel,
so its original order divides the quotient order times the kernel order. -/
theorem orderOf_dvd_orderOf_quotient_mul_card (N : Subgroup G) [N.Normal] (x : G) :
    orderOf x ∣ orderOf (QuotientGroup.mk' N x) * Nat.card N := by
  apply orderOf_dvd_of_pow_eq_one
  rw [pow_mul]
  have hx : x ^ orderOf (QuotientGroup.mk' N x) ∈ N := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' N (x ^ orderOf (QuotientGroup.mk' N x)) = 1
    rw [map_pow, pow_orderOf_eq_one]
  exact orderOf_dvd_iff_pow_eq_one.mp (N.orderOf_dvd_natCard hx)

/-- A quotient with kernel of order coprime to `p` preserves divisibility of
element orders by `p`. The elementary argument works without assuming primality. -/
theorem dvd_orderOf_quotient_iff (N : Subgroup G) [N.Normal] {p : ℕ}
    (hN : (Nat.card N).Coprime p) (x : G) :
    p ∣ orderOf (QuotientGroup.mk' N x) ↔ p ∣ orderOf x := by
  constructor
  · intro hx
    exact hx.trans (orderOf_map_dvd (QuotientGroup.mk' N) x)
  · intro hx
    exact hN.symm.dvd_mul_right.mp (hx.trans (orderOf_dvd_orderOf_quotient_mul_card N x))

/-- The original single-value hypothesis passes to a quotient by a normal
subgroup whose order is coprime to `p`. -/
theorem ProductOrderCondition.quotient
    {w : OuterWord} {p : ℕ} (h : ProductOrderCondition w p G)
    (N : Subgroup G) [N.Normal] (hN : (Nat.card N).Coprime p) :
    ProductOrderCondition w p (G ⧸ N) := by
  let f : G →* G ⧸ N := QuotientGroup.mk' N
  have hvalues : f '' w.values G = w.values (G ⧸ N) :=
    w.image_values_eq f (QuotientGroup.mk'_surjective N)
  have hord (a : G) : p ∣ orderOf (f a) ↔ p ∣ orderOf a :=
    dvd_orderOf_quotient_iff N hN a
  intro x hx y hy hxp hyp
  rw [← hvalues] at hx hy
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  have hap : ¬ p ∣ orderOf a := fun ha' => hxp ((hord a).2 ha')
  have hbp : p ∣ orderOf b := (hord b).1 hyp
  have hab : p ∣ orderOf (a * b) := h a ha b hb hap hbp
  simpa only [map_mul] using (hord (a * b)).2 hab

end Kourovka2135
