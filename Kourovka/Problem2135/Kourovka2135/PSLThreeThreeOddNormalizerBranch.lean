import Kourovka2135.SL33OrderFourGoodSet
import Kourovka2135.OddNormalizerModelObstruction

/-! The actual PSL(3,3) quotient excludes every odd-prime least exception
whose soluble radical is noncentral. The order-four good class and the
concrete semidihedral two-subgroup discharge the normalizer interface. -/

set_option autoImplicit false
namespace Kourovka2135

theorem OrderMinimalException.false_of_odd_noncentral_pslThreeThree_quotient
    {E : Type*} [Group E] [Finite E] {w : OuterWord} {p : ℕ}
    (h : OrderMinimalException w p E) (hp : p.Prime) (hodd : p ≠ 2)
    (hnoncentral : ¬ solubleRadical E ≤ Subgroup.center E)
    (e : (E ⧸ solubleRadical E) ≃* PSLThreeThreeSemidihedralData.Q) : False := by
  have hP : IsPGroup 2 PSLThreeThreeSemidihedralData.subgroup :=
    IsPGroup.of_card (n := 4) (by simpa using PSLThreeThreeSemidihedralData.subgroup_card)
  exact h.false_of_odd_model_normalizer_good_set hp Nat.prime_two hodd hodd.symm
    hnoncentral (e.trans PSLThreeThreeSemidihedralData.projectiveEquiv.symm)
    SL33OrderFourGoodSet.goodClass PSLThreeThreeSemidihedralData.subgroup hP
    SL33OrderFourGoodSet.a PSLThreeThreeSemidihedralData.x
    (IsConj.refl _) SL33OrderFourGoodSet.normalizes
    PSLThreeThreeSemidihedralData.sx.property SL33OrderFourGoodSet.double_commutator_ne_one

end Kourovka2135
