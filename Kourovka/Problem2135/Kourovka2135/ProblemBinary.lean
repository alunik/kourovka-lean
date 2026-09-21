import Kourovka2135.SuzukiBinaryComplete
import Kourovka2135.BinarySuzukiReduction
import Kourovka2135.MinimalExistence
import Mathlib.Algebra.Group.Shrink
import Mathlib.Data.Fintype.Shrink

/-! Kourovka 21.35 at the prime two for every outer commutator word and every
finite group. Thompson's minimal-simple classification is the only external
mathematical parameter. The hypothesis concerns single word values and allows
the second value to have arbitrary even order. -/

set_option autoImplicit false
universe u
noncomputable section
namespace Kourovka2135

/-- There are no binary order-minimal exceptions. -/
theorem OrderMinimalException.false_two
    (classification : MinimalSimpleClassification.{0})
    {G : Type} [Group G] [Finite G] {w : OuterWord}
    (h : OrderMinimalException w 2 G) : False := by
  obtain ⟨m, hm, _, ⟨e⟩⟩ := h.exists_suzuki_quotient_two classification
  exact h.false_of_binary_suzuki_quotient classification m hm e

/-- The full prime-two forward implication, for arbitrary outer-word bracketing. -/
private theorem problem2135_binary_outerWord_small
    (classification : MinimalSimpleClassification.{0})
    {G : Type} [Group G] [Finite G] (w : OuterWord)
    (h : ProductOrderCondition w 2 G) :
    HasNormalPComplement 2 (w.verbalSubgroup G) := by
  by_contra hf
  obtain ⟨H, groupH, finiteH, hex⟩ := exists_orderMinimalException h hf
  let : Group H := groupH
  let : Finite H := finiteH
  exact hex.false_two classification

/-- The prime-two endpoint in every universe, by transport to an actual finite
small group. The word and its single-value order condition are unchanged. -/
theorem problem2135_binary_outerWord
    (classification : MinimalSimpleClassification.{0})
    {G : Type u} [Group G] [Finite G] (w : OuterWord)
    (h : ProductOrderCondition w 2 G) :
    HasNormalPComplement 2 (w.verbalSubgroup G) := by
  let e : Shrink.{0} G ≃* G := Shrink.mulEquiv
  have hs : ProductOrderCondition w 2 (Shrink.{0} G) := by
    intro x hx y hy hxp hyp
    have hxp' : ¬ 2 ∣ orderOf (e x) := by rwa [e.orderOf_eq]
    have hyp' : 2 ∣ orderOf (e y) := by rwa [e.orderOf_eq]
    have hz := h (e x) (w.map_mem_values e.toMonoidHom hx)
      (e y) (w.map_mem_values e.toMonoidHom hy) hxp' hyp'
    simpa only [← map_mul, e.orderOf_eq] using hz
  have hc := problem2135_binary_outerWord_small classification w hs
  let f : w.verbalSubgroup G →* w.verbalSubgroup (Shrink.{0} G) := {
    toFun := fun x => ⟨e.symm (x : G),
      w.map_verbalSubgroup_le e.symm.toMonoidHom ⟨x, x.property, rfl⟩⟩
    map_one' := Subtype.ext (map_one e.symm)
    map_mul' := fun _ _ => Subtype.ext (map_mul e.symm _ _) }
  apply hc.of_injective Nat.prime_two f
  intro x y hxy
  apply Subtype.ext
  apply e.symm.injective
  exact congrArg Subtype.val hxy

/-- The binary condition is equivalent to a normal two-complement in the
actual verbal subgroup, retaining the full single-value hypothesis. -/
theorem productOrderCondition_two_iff_hasNormalPComplement
    (classification : MinimalSimpleClassification.{0})
    {G : Type u} [Group G] [Finite G] (w : OuterWord) :
    ProductOrderCondition w 2 G ↔ HasNormalPComplement 2 (w.verbalSubgroup G) :=
  ⟨problem2135_binary_outerWord classification w,
    productOrderCondition_of_hasNormalPComplement Nat.prime_two⟩

end Kourovka2135
