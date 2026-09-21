import Kourovka2135.BinaryFourFrattiniValues
import Kourovka2135.SplitTorusPrimeConjugacy
import Kourovka2135.BinarySplitGoodSetObstruction

/-! The complete four-parameter binary Frattini obstruction. An actual
order-three universal value has a nonidentity split-torus image, contradicting
the proved derived-value centralization theorem. -/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135

theorem not_productOrderCondition_of_binary_four_frattini
    {F : Type} [Field F] [Fintype F] [CharP F 2]
    [IsSimpleGroup (SLTwo.SL2 F)]
    (hcard : Fintype.card F = 4)
    (hsolv : ∀ H : Subgroup (SLTwo.SL2 F), H < ⊤ → Group.IsSolvable H)
    {G : Type} [Group G] [Finite G] [Group.IsPerfect G]
    (pi : G →* SLTwo.SL2 F) (hpi : Function.Surjective pi)
    (hR : IsPGroup 2 pi.ker) (hF : pi.ker ≤ frattini G) (w : OuterWord) :
    ¬ ProductOrderCondition w 2 G := by
  intro h
  obtain ⟨x, hxorder, hx⟩ := BinaryFourFrattiniValues.exists_order_three_universal_value
    hcard hsolv pi hpi hR hF
  let e := QuotientGroup.quotientKerEquivOfSurjective pi hpi
  have hmaporder : orderOf (pi x) = 3 := by
    change orderOf (e (QuotientGroup.mk' pi.ker x)) = 3
    rw [e.orderOf_eq,
      orderOf_quotient_eq_of_coprime_pgroup Nat.prime_two pi.ker hR x]
    · exact hxorder
    · rw [hxorder]
      decide
  obtain ⟨a, haorder, haconj⟩ :=
    SplitTorusPrimeConjugacy.mem_splitOrderSet_three_of_fintype_card_four hcard (pi x) hmaporder
  have hane : a ≠ 1 := by
    intro heq
    rw [heq, orderOf_one] at haorder
    omega
  have hd : ProductOrderCondition (OuterWord.derivedWord w.height) 2 G := by
    intro a ha b hb hap hbp
    exact h a (w.derivedWord_values_subset w.height le_rfl ha)
      b (w.derivedWord_values_subset w.height le_rfl hb) hap hbp
  exact BinarySplitGoodSetObstruction.false_of_odd_derived_value_split_image
    pi hpi hR w.height hd x (hx _) (by rw [hxorder]; decide) a hane haconj

end Kourovka2135
