import Kourovka2135.OddGeneratingGoodSet
import Kourovka2135.DerivedCentralization

/-! An actual even-order iterated commutator rules out the binary product-order
condition when an odd generating good set maps into its conjugacy class. -/

set_option autoImplicit false
noncomputable section
universe u v
namespace Kourovka2135.OddGoodSetTripleObstruction

theorem not_productOrderCondition
    {G : Type u} {Q : Type v} [Group G] [Group Q]
    (π : G →* Q) (hπ : Function.Surjective π) (B : Set Q)
    (hgood : HasOddGeneratingGoodSetOver π B) (a z : Q)
    (hclass : ∀ g ∈ B, IsConj a g)
    (heven : 2 ∣ orderOf (paperCommutator (paperCommutator z a) a))
    (w : OuterWord) : ¬ ProductOrderCondition w 2 G := by
  intro h
  obtain ⟨x, hx, hxB, hxodd⟩ := hgood.exists_value (OuterWord.derivedWord w.height)
  obtain ⟨s, hs⟩ := isConj_iff.mp (hclass (π x) hxB)
  obtain ⟨t, ht⟩ := hπ s
  let y := t⁻¹ * x * t
  have hy : y ∈ (OuterWord.derivedWord w.height).values G :=
    (OuterWord.derivedWord w.height).conj_mem_values hx t
  have hyorder : orderOf y = orderOf x := by
    simpa only [y, MulAut.conj_apply, inv_inv] using (MulAut.conj t⁻¹).orderOf_eq x
  have hyp : ¬ 2 ∣ orderOf y := by
    rw [hyorder]
    exact hxodd.not_two_dvd_nat
  have hiy : π y = a := by
    change π (t⁻¹ * x * t) = a
    rw [map_mul, map_mul, map_inv, ht, ← hs]
    group
  have hd : ProductOrderCondition (OuterWord.derivedWord w.height) 2 G := by
    intro b hb c hc hbp hcp
    exact h b (w.derivedWord_values_subset w.height le_rfl hb)
      c (w.derivedWord_values_subset w.height le_rfl hc) hbp hcp
  obtain ⟨r, hr⟩ := hπ z
  have hnot := hd.not_dvd_orderOf_tripleCommutator hy hyp r
  have himage : π (paperCommutator (paperCommutator r y) y) =
      paperCommutator (paperCommutator z a) a := by
    simp only [paperCommutator, map_mul, map_inv, hr, hiy]
  have hdiv := orderOf_map_dvd π (paperCommutator (paperCommutator r y) y)
  rw [himage] at hdiv
  exact hnot (heven.trans hdiv)

end Kourovka2135.OddGoodSetTripleObstruction
