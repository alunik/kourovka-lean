import Kourovka2135.OuterWord
import Kourovka2135.Complement

/-!
# The exact statement of Kourovka Notebook 21.35

`Problem2135 G` is the requested forward implication. Defining this proposition
does not prove it. The theorem proved here is its converse, with no restriction
on the bracketing of the word or on the p-part of the second value.
-/

set_option autoImplicit false

universe u

namespace Kourovka2135

/-- The problem's condition on two single word values. The second value may
have mixed order; it need not have prime-power order. -/
def ProductOrderCondition (w : OuterWord) (p : ℕ) (G : Type u) [Group G] : Prop :=
  ∀ x ∈ w.values G, ∀ y ∈ w.values G,
    ¬ p ∣ orderOf x → p ∣ orderOf y → p ∣ orderOf (x * y)

/-- The full forward assertion for a given finite group. No proof of this
proposition is supplied by its definition. -/
def Problem2135 (G : Type u) [Group G] [Finite G] : Prop :=
  ∀ (w : OuterWord) (p : ℕ), p.Prime → ProductOrderCondition w p G →
    HasNormalPComplement p (w.verbalSubgroup G)

/-- The converse of 21.35, for every outer commutator word. -/
theorem productOrderCondition_of_hasNormalPComplement
    {w : OuterWord} {p : ℕ} (hp : p.Prime)
    {G : Type u} [Group G] [Finite G]
    (h : HasNormalPComplement p (w.verbalSubgroup G)) :
    ProductOrderCondition w p G := by
  intro x hx y hy hxp hyp
  let x' : w.verbalSubgroup G := ⟨x, w.mem_verbalSubgroup_of_mem_values hx⟩
  let y' : w.verbalSubgroup G := ⟨y, w.mem_verbalSubgroup_of_mem_values hy⟩
  have hx' : (orderOf x').Coprime p := by
    simpa only [x', Subgroup.orderOf_mk] using (hp.coprime_iff_not_dvd.mpr hxp).symm
  have hy' : p ∣ orderOf y' := by simpa only [y', Subgroup.orderOf_mk] using hyp
  have hxy := product_order_condition_of_hasNormalPComplement hp h hx' hy'
  simpa only [← Subgroup.orderOf_coe, Subgroup.coe_mul, x', y'] using hxy

/-- The hypothesis passes to every subgroup, with the same single word. -/
theorem ProductOrderCondition.subgroup
    {w : OuterWord} {p : ℕ} {G : Type u} [Group G]
    (h : ProductOrderCondition w p G) (H : Subgroup G) :
    ProductOrderCondition w p H := by
  intro x hx y hy hxp hyp
  have hxG := w.map_mem_values H.subtype hx
  have hyG := w.map_mem_values H.subtype hy
  have hxpG : ¬ p ∣ orderOf (x : G) := by simpa using hxp
  have hypG : p ∣ orderOf (y : G) := by simpa using hyp
  simpa only [← Subgroup.orderOf_coe, Subgroup.coe_mul] using
    h (x : G) hxG (y : G) hyG hxpG hypG

/-- The forward conclusion holds for every word in a finite p-group. -/
theorem verbalSubgroup_hasNormalPComplement_of_isPGroup
    {p : ℕ} (hp : p.Prime) {G : Type u} [Group G] [Finite G]
    (hG : IsPGroup p G) (w : OuterWord) :
    HasNormalPComplement p (w.verbalSubgroup G) :=
  hasNormalPComplement_of_isPGroup hp (hG.to_subgroup (w.verbalSubgroup G))

end Kourovka2135
