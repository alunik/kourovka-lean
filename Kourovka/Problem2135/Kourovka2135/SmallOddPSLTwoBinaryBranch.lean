import Kourovka2135.OddPSLTwoSplitThreeFrattini
import Kourovka2135.OddPSLTwoCentralKernel
import Kourovka2135.SmallOddPSLTwoTripleObstruction
import Kourovka2135.BinarySLTwoMinimalException

/-! Complete binary least-exception exclusions for actual PSL2(F7) and
PSL2(F13). The only classification input is the explicit permitted Thompson
statement, used solely to derive solubility of proper quotient subgroups. -/

set_option autoImplicit false
noncomputable section
namespace Kourovka2135
open OddPSLTwoProjectiveChart

theorem not_productOrderCondition_of_binary_frattini_pslTwo7
    (hsolv : ∀ H : Subgroup (Q (ZMod 7)), H < ⊤ → Group.IsSolvable H)
    {G : Type} [Group G] [Finite G] [Group.IsPerfect G]
    (π : G →* Q (ZMod 7)) (hπ : Function.Surjective π)
    (hR : IsPGroup 2 π.ker) (hRΦ : π.ker ≤ frattini G) (w : OuterWord) :
    ¬ ProductOrderCondition w 2 G := by
  have hodd : Odd (Nat.card (ZMod 7)) := by
    norm_num [Nat.card_eq_fintype_card, ZMod.card]
  have hg : HasOddGeneratingGoodSetOver π
      (OddPSLTwoSplitThreeFrattini.projectiveGoodSet (ZMod 7)) := by
    exact OddPSLTwoSplitThreeFrattini.hasOddGeneratingGoodSetOver_seven hsolv
      (OddPSLTwoCentralKernel.kernelBound (ZMod 7) hodd) π hπ hR hRΦ
  apply OddGoodSetTripleObstruction.not_productOrderCondition π hπ
    (OddPSLTwoSplitThreeFrattini.projectiveGoodSet (ZMod 7)) hg
    (quotient (ZMod 7) SmallOddPSLTwoTripleObstruction.Q7.a)
    (quotient (ZMod 7) SmallOddPSLTwoTripleObstruction.Q7.z) ?_
    SmallOddPSLTwoTripleObstruction.Q7.two_dvd_orderOf_tripleCommutator w
  intro g hg
  obtain ⟨x, hx, rfl⟩ := hg
  exact SmallOddPSLTwoTripleObstruction.Q7.isConj_of_mem_splitOrderSet hx

theorem OrderMinimalException.false_of_binary_pslTwo7_quotient_complete
    {G : Type} [Group G] [Finite G] {w : OuterWord}
    (classification : MinimalSimpleClassification.{0})
    (h : OrderMinimalException w 2 G)
    (e : (G ⧸ solubleRadical G) ≃* Q (ZMod 7)) : False := by
  let : Group.IsPerfect G := h.isPerfect Nat.prime_two
  let π := e.toMonoidHom.comp (QuotientGroup.mk' (solubleRadical G))
  have hπ : Function.Surjective π :=
    e.surjective.comp (QuotientGroup.mk'_surjective (solubleRadical G))
  have hker : π.ker = solubleRadical G := by
    exact (MonoidHom.ker_mulEquiv_comp (QuotientGroup.mk' (solubleRadical G)) e).trans
      (QuotientGroup.ker_mk' (solubleRadical G))
  have hR : IsPGroup 2 π.ker := by
    rw [hker, h.radical_eq_pCore Nat.prime_two]
    exact pCore_isPGroup
  have hF : π.ker ≤ frattini G := by
    rw [hker]
    exact h.radical_le_frattini Nat.prime_two
  exact not_productOrderCondition_of_binary_frattini_pslTwo7
    (proper_subgroups_solvable_of_equiv e
      (h.quotient_radical_proper_subgroup_isSolvable_two classification))
    π hπ hR hF w h.condition

theorem not_productOrderCondition_of_binary_frattini_pslTwo13
    (hsolv : ∀ H : Subgroup (Q (ZMod 13)), H < ⊤ → Group.IsSolvable H)
    {G : Type} [Group G] [Finite G] [Group.IsPerfect G]
    (π : G →* Q (ZMod 13)) (hπ : Function.Surjective π)
    (hR : IsPGroup 2 π.ker) (hRΦ : π.ker ≤ frattini G) (w : OuterWord) :
    ¬ ProductOrderCondition w 2 G := by
  have hodd : Odd (Nat.card (ZMod 13)) := by
    norm_num [Nat.card_eq_fintype_card, ZMod.card]
  have hg : HasOddGeneratingGoodSetOver π
      (OddPSLTwoSplitThreeFrattini.projectiveGoodSet (ZMod 13)) := by
    exact OddPSLTwoSplitThreeFrattini.hasOddGeneratingGoodSetOver (ZMod 13) hodd
      (by norm_num [Nat.card_eq_fintype_card, ZMod.card])
      (by norm_num [Nat.card_eq_fintype_card, ZMod.card]) hsolv
      (OddPSLTwoCentralKernel.kernelBound (ZMod 13) hodd) π hπ hR hRΦ
  apply OddGoodSetTripleObstruction.not_productOrderCondition π hπ
    (OddPSLTwoSplitThreeFrattini.projectiveGoodSet (ZMod 13)) hg
    (quotient (ZMod 13) SmallOddPSLTwoTripleObstruction.Q13.a)
    (quotient (ZMod 13) SmallOddPSLTwoTripleObstruction.Q13.z) ?_
    SmallOddPSLTwoTripleObstruction.Q13.two_dvd_orderOf_tripleCommutator w
  intro g hg
  obtain ⟨x, hx, rfl⟩ := hg
  exact SmallOddPSLTwoTripleObstruction.Q13.isConj_of_mem_splitOrderSet hx

theorem OrderMinimalException.false_of_binary_pslTwo13_quotient_complete
    {G : Type} [Group G] [Finite G] {w : OuterWord}
    (classification : MinimalSimpleClassification.{0})
    (h : OrderMinimalException w 2 G)
    (e : (G ⧸ solubleRadical G) ≃* Q (ZMod 13)) : False := by
  let : Group.IsPerfect G := h.isPerfect Nat.prime_two
  let π := e.toMonoidHom.comp (QuotientGroup.mk' (solubleRadical G))
  have hπ : Function.Surjective π :=
    e.surjective.comp (QuotientGroup.mk'_surjective (solubleRadical G))
  have hker : π.ker = solubleRadical G := by
    exact (MonoidHom.ker_mulEquiv_comp (QuotientGroup.mk' (solubleRadical G)) e).trans
      (QuotientGroup.ker_mk' (solubleRadical G))
  have hR : IsPGroup 2 π.ker := by
    rw [hker, h.radical_eq_pCore Nat.prime_two]
    exact pCore_isPGroup
  have hF : π.ker ≤ frattini G := by
    rw [hker]
    exact h.radical_le_frattini Nat.prime_two
  exact not_productOrderCondition_of_binary_frattini_pslTwo13
    (proper_subgroups_solvable_of_equiv e
      (h.quotient_radical_proper_subgroup_isSolvable_two classification))
    π hπ hR hF w h.condition

end Kourovka2135
