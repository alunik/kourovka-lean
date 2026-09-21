import Kourovka2135.ProblemRemaining
import Kourovka2135.CentralQuasisimpleComplete

/-! The full Kourovka 21.35 implication, conditional only on Thompson's
minimal-simple classification and the uniform quasisimple coprime commutator
assertion. Neither assumption is installed as an axiom or a typeclass. -/

set_option autoImplicit false
universe u
noncomputable section
namespace Kourovka2135

/-- The two explicitly named mathematical hypotheses exclude every least
exception, for every prime and every outer word. -/
theorem OrderMinimalException.false
    (classification : MinimalSimpleClassification.{0})
    (quasisimple : QuasisimpleCoprimeCommutators.{0})
    {G : Type} [Group G] [Finite G] {w : OuterWord} {p : ℕ}
    (h : OrderMinimalException w p G) (hp : p.Prime) : False := by
  exact h.false_of_radical_le_center quasisimple hp
    (h.odd_and_radical_le_center classification hp).2

private theorem problem2135_outerWord_small
    (classification : MinimalSimpleClassification.{0})
    (quasisimple : QuasisimpleCoprimeCommutators.{0})
    {G : Type} [Group G] [Finite G] (w : OuterWord) (p : ℕ) (hp : p.Prime)
    (h : ProductOrderCondition w p G) :
    HasNormalPComplement p (w.verbalSubgroup G) := by
  by_contra hf
  obtain ⟨H, groupH, finiteH, hex⟩ := exists_orderMinimalException h hf
  let : Group H := groupH
  let : Finite H := finiteH
  exact hex.false classification quasisimple hp

/-- The full forward implication for an arbitrary finite group, prime, and
outer commutator word, retaining the original single-value hypothesis. -/
theorem problem2135_outerWord
    (classification : MinimalSimpleClassification.{0})
    (quasisimple : QuasisimpleCoprimeCommutators.{0})
    {G : Type u} [Group G] [Finite G] (w : OuterWord) (p : ℕ) (hp : p.Prime)
    (h : ProductOrderCondition w p G) :
    HasNormalPComplement p (w.verbalSubgroup G) := by
  let e : Shrink.{0} G ≃* G := Shrink.mulEquiv
  have hs : ProductOrderCondition w p (Shrink.{0} G) := by
    intro x hx y hy hxp hyp
    have hxp' : ¬ p ∣ orderOf (e x) := by rwa [e.orderOf_eq]
    have hyp' : p ∣ orderOf (e y) := by rwa [e.orderOf_eq]
    have hz := h (e x) (w.map_mem_values e.toMonoidHom hx)
      (e y) (w.map_mem_values e.toMonoidHom hy) hxp' hyp'
    simpa only [← map_mul, e.orderOf_eq] using hz
  have hc := problem2135_outerWord_small classification quasisimple w p hp hs
  let f : w.verbalSubgroup G →* w.verbalSubgroup (Shrink.{0} G) := {
    toFun := fun x => ⟨e.symm (x : G),
      w.map_verbalSubgroup_le e.symm.toMonoidHom ⟨x, x.property, rfl⟩⟩
    map_one' := Subtype.ext (map_one e.symm)
    map_mul' := fun _ _ => Subtype.ext (map_mul e.symm _ _) }
  apply hc.of_injective hp f
  intro x y hxy
  apply Subtype.ext
  apply e.symm.injective
  exact congrArg Subtype.val hxy

/-- The exact requested problem, for all finite groups and all outer words,
under precisely the two explicit mathematical assumptions. -/
theorem problem2135
    (classification : MinimalSimpleClassification.{0})
    (quasisimple : QuasisimpleCoprimeCommutators.{0})
    (G : Type u) [Group G] [Finite G] : Problem2135 G := by
  intro w p hp h
  exact problem2135_outerWord classification quasisimple w p hp h

/-- The original single-value product-order condition is equivalent to a
normal p-complement in the actual verbal subgroup. -/
theorem productOrderCondition_iff_hasNormalPComplement
    (classification : MinimalSimpleClassification.{0})
    (quasisimple : QuasisimpleCoprimeCommutators.{0})
    {G : Type u} [Group G] [Finite G] (w : OuterWord) (p : ℕ) (hp : p.Prime) :
    ProductOrderCondition w p G ↔ HasNormalPComplement p (w.verbalSubgroup G) :=
  ⟨problem2135_outerWord classification quasisimple w p hp,
    productOrderCondition_of_hasNormalPComplement hp⟩

end Kourovka2135
