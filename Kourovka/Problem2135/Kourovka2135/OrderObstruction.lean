import Kourovka2135.Statement

/-!
# An elementary forward obstruction

Under the product-order condition, a commutator `[x,g]` that is itself a
single word value cannot have order divisible by p if x is a p′-order single
word value. This does not claim that an arbitrary such commutator is a word
value: that membership remains an explicit hypothesis.
-/

set_option autoImplicit false

universe u

namespace Kourovka2135

theorem ProductOrderCondition.not_dvd_orderOf_commutator
    {w : OuterWord} {p : ℕ} {G : Type u} [Group G]
    (h : ProductOrderCondition w p G) {x g : G}
    (hx : x ∈ w.values G) (hxp : ¬ p ∣ orderOf x)
    (hc : x⁻¹ * g⁻¹ * x * g ∈ w.values G) :
    ¬ p ∣ orderOf (x⁻¹ * g⁻¹ * x * g) := by
  intro hcp
  have hproduct := h x hx (x⁻¹ * g⁻¹ * x * g) hc hxp hcp
  have horder : orderOf (g⁻¹ * x * g) = orderOf x := by
    simpa only [MulAut.conj_apply, inv_inv] using (MulAut.conj g⁻¹).orderOf_eq x
  have hmul : x * (x⁻¹ * g⁻¹ * x * g) = g⁻¹ * x * g := by simp [mul_assoc]
  rw [hmul, horder] at hproduct
  exact hxp hproduct

theorem ProductOrderCondition.commutator_eq_one_of_mem_pSubgroup
    {w : OuterWord} {p : ℕ} (hp : p.Prime)
    {G : Type u} [Group G] (h : ProductOrderCondition w p G)
    {x g : G} (hx : x ∈ w.values G) (hxp : ¬ p ∣ orderOf x)
    (hc : x⁻¹ * g⁻¹ * x * g ∈ w.values G)
    (P : Subgroup G) (hP : IsPGroup p P)
    (hcP : x⁻¹ * g⁻¹ * x * g ∈ P) :
    x⁻¹ * g⁻¹ * x * g = 1 := by
  let : Fact p.Prime := ⟨hp⟩
  by_contra hne
  have hneP : (⟨x⁻¹ * g⁻¹ * x * g, hcP⟩ : P) ≠ 1 := by
    intro heq
    exact hne (congrArg Subtype.val heq)
  have hdiv := hP.dvd_orderOf hneP
  have hnot := h.not_dvd_orderOf_commutator hx hxp hc
  exact hnot (by simpa only [Subgroup.orderOf_mk] using hdiv)

theorem ProductOrderCondition.commute_of_commutator_mem_pSubgroup
    {w : OuterWord} {p : ℕ} (hp : p.Prime)
    {G : Type u} [Group G] (h : ProductOrderCondition w p G)
    {x g : G} (hx : x ∈ w.values G) (hxp : ¬ p ∣ orderOf x)
    (hc : x⁻¹ * g⁻¹ * x * g ∈ w.values G)
    (P : Subgroup G) (hP : IsPGroup p P)
    (hcP : x⁻¹ * g⁻¹ * x * g ∈ P) : Commute x g := by
  have heq := h.commutator_eq_one_of_mem_pSubgroup hp hx hxp hc P hP hcP
  have hmul := congrArg (fun z : G => g * x * z) heq
  change x * g = g * x
  simpa only [mul_assoc, mul_inv_cancel_left, mul_one] using hmul

end Kourovka2135
