import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.QuotientGroup.Basic

set_option autoImplicit false

universe u
namespace Kourovka2135

/-- A normal subgroup of order prime to `p` and index a power of `p`.
This is the usual normal p-complement, not a normal Sylow p-subgroup. -/
def HasNormalPComplement (p : ℕ) (G : Type u) [Group G] : Prop :=
  ∃ N : Subgroup G, N.Normal ∧ (Nat.card N).Coprime p ∧ ∃ n : ℕ, N.index = p ^ n

/-- A normal p-complement forces the product-order condition for all elements. -/
theorem product_order_condition_of_hasNormalPComplement
    {p : ℕ} (hp : p.Prime) {G : Type u} [Group G] [Finite G]
    (hG : HasNormalPComplement p G) {x y : G}
    (hx : (orderOf x).Coprime p) (hy : p ∣ orderOf y) :
    p ∣ orderOf (x * y) := by
  obtain ⟨N, hN, hcard, n, hindex⟩ := hG
  let : N.Normal := hN
  let : Fact p.Prime := ⟨hp⟩
  let f : G →* G ⧸ N := QuotientGroup.mk' N
  have hP : IsPGroup p (G ⧸ N) := IsPGroup.of_card (by
    rw [← N.index_eq_card]
    exact hindex)
  have hfx : f x = 1 := by
    by_contra hne
    have hd : p ∣ orderOf x := (hP.dvd_orderOf hne).trans (orderOf_map_dvd f x)
    exact (hp.coprime_iff_not_dvd.mp hx.symm) hd
  have hfy : f y ≠ 1 := by
    intro heq
    have hyN : y ∈ N := (QuotientGroup.eq_one_iff y).mp heq
    have hd : p ∣ Nat.card N := hy.trans (N.orderOf_dvd_natCard hyN)
    exact (hp.coprime_iff_not_dvd.mp hcard.symm) hd
  have hfxy : f (x * y) ≠ 1 := by simpa [map_mul, hfx] using hfy
  exact (hP.dvd_orderOf hfxy).trans (orderOf_map_dvd f (x * y))

/-- A finite p-group has the trivial normal p-complement. -/
theorem hasNormalPComplement_of_isPGroup
    {p : ℕ} (hp : p.Prime) {G : Type u} [Group G] [Finite G]
    (hG : IsPGroup p G) : HasNormalPComplement p G := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hG
  refine ⟨⊥, inferInstance, by simp, n, ?_⟩
  simpa using hn

/-- A finite group of order prime to p is its own normal p-complement. -/
theorem hasNormalPComplement_of_coprime_card
    {p : ℕ} {G : Type u} [Group G]
    (hG : (Nat.card G).Coprime p) : HasNormalPComplement p G := by
  refine ⟨⊤, inferInstance, ?_, 0, by simp⟩
  simpa using hG

#print axioms product_order_condition_of_hasNormalPComplement
#print axioms hasNormalPComplement_of_isPGroup
#print axioms hasNormalPComplement_of_coprime_card
end Kourovka2135
