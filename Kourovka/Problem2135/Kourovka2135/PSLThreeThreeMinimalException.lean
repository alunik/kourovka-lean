import Kourovka2135.PSLThreeThreeOrderObstruction
import Kourovka2135.MinimalFrattini

/-! Conditional removal of the actual PSL3(F3) branch of a least exception.
All structural hypotheses are derived from leastness and the displayed
quotient equivalence. The only unfinished input is `BinaryModuleBound`.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135

/-- No classification parameter is required after the actual quotient has
been identified. The representation bound remains an explicit hypothesis. -/
theorem OrderMinimalException.false_of_binary_pslThreeThree_quotient
    (hmodule : PSLThreeThreeFrattiniLifting.BinaryModuleBound)
    {G : Type} [Group G] [Finite G] {w : OuterWord}
    (h : OrderMinimalException w 2 G)
    (e : (G ⧸ solubleRadical G) ≃* PSL33GoodSets.Q) : False := by
  let : Group.IsPerfect G := h.isPerfect Nat.prime_two
  let : IsSimpleGroup (G ⧸ solubleRadical G) := h.quotient_radical_isSimple Nat.prime_two
  let : IsSimpleGroup PSL33GoodSets.Q := e.symm.isSimpleGroup
  let pi := e.toMonoidHom.comp (QuotientGroup.mk' (solubleRadical G))
  have hpi : Function.Surjective pi :=
    e.surjective.comp (QuotientGroup.mk'_surjective (solubleRadical G))
  have hker : pi.ker = solubleRadical G := by
    exact (MonoidHom.ker_mulEquiv_comp (QuotientGroup.mk' (solubleRadical G)) e).trans
      (QuotientGroup.ker_mk' (solubleRadical G))
  have hR : IsPGroup 2 pi.ker := by
    rw [hker, h.radical_eq_pCore Nat.prime_two]
    exact pCore_isPGroup
  have hF : pi.ker ≤ frattini G := by
    rw [hker]
    exact h.radical_le_frattini Nat.prime_two
  exact PSLThreeThreeOrderObstruction.not_productOrderCondition
    hmodule pi hpi hR hF w h.condition

end Kourovka2135
