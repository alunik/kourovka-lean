import Kourovka2135.CentralDoubleCoverCases
import Kourovka2135.OddPSLTwoCentralKernel
import Kourovka2135.OddSLTwoCenter
import Kourovka2135.SLTwoTetrahedralObstruction
import Kourovka2135.MinimalFrattini

/-! Central binary covers of actual PSL2 over odd finite fields violate the
binary product-order condition. The actual reference SL2 is perfect, its
center has size two, and the checked central-kernel bound identifies every
finite perfect central binary cover with SL2 or PSL2. Explicit quaternion
and tetrahedral word values obstruct the condition in both groups.

No subgroup classification, Frattini hypothesis, or solubility premise is
needed for the cover theorem. The final least-exception corollary uses only
the genuine centrality of the soluble radical and its actual quotient.
-/

set_option autoImplicit false
noncomputable section
namespace Kourovka2135.OddPSLTwoCentralObstruction

open OddPSLTwoProjectiveChart

variable (F : Type) [Field F] [Finite F]

theorem reference_isPerfect (hcard : 3 < Nat.card F) :
    Group.IsPerfect (SLTwo.SL2 F) := by
  obtain ⟨s, hs⟩ := exists_pow_ne_one_of_isCyclic (G := Fˣ)
    (by decide : (2 : ℕ) ≠ 0) (show 2 < Nat.card Fˣ by rw [Nat.card_units]; omega)
  refine ⟨Matrix.SL2.commutator_eq_top (Units.ne_zero s) ?_⟩
  intro h
  apply hs
  apply Units.ext
  simpa only [Units.val_pow_eq_pow_val, Units.val_one] using h

/-- Every actual finite perfect central binary cover has the explicit
matrix-group obstruction, with no temporary kernel-bound input. -/
theorem not_productOrderCondition (hodd : Odd (Nat.card F))
    (hcard : 3 < Nat.card F)
    {G : Type} [Group G] [Finite G] [Group.IsPerfect G]
    (π : G →* Q F) (hπ : Function.Surjective π)
    (hbinary : IsPGroup 2 π.ker) (hcentral : π.ker ≤ Subgroup.center G)
    (w : OuterWord) : ¬ ProductOrderCondition w 2 G := by
  let : Group.IsPerfect (SLTwo.SL2 F) := reference_isPerfect F hcard
  have href := SLTwoTetrahedralObstruction.not_productOrderCondition
    hcard (OddSLTwoCenter.ringChar_ne_two F hodd) w
  rcases CentralDoubleCoverUniqueness.exists_equiv_reference_or_base
    (OddPSLTwoCentralKernel.kernelBound F hodd) (quotient F)
    (QuotientGroup.mk'_surjective _)
    (by change (QuotientGroup.mk' (Subgroup.center (SLTwo.SL2 F))).ker ≤ _; simp)
    (OddSLTwoCenter.card_ker_quotient F hodd) π hπ hbinary hcentral with hE | hQ
  · obtain ⟨e⟩ := hE
    intro h
    exact href.1 (h.of_injective e.symm.toMonoidHom e.symm.injective)
  · obtain ⟨e⟩ := hQ
    intro h
    exact href.2 (h.of_injective e.symm.toMonoidHom e.symm.injective)

end Kourovka2135.OddPSLTwoCentralObstruction

namespace Kourovka2135
open OddPSLTwoProjectiveChart

/-- A least binary exception with central radical cannot have an actual
odd PSL2 quotient. There is no classification premise. -/
theorem OrderMinimalException.false_of_central_radical_odd_pslTwo_quotient
    {G : Type} [Group G] [Finite G] {w : OuterWord}
    (h : OrderMinimalException w 2 G)
    {F : Type} [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) (hcard : 3 < Nat.card F)
    (hcentral : solubleRadical G ≤ Subgroup.center G)
    (e : (G ⧸ solubleRadical G) ≃* Q F) : False := by
  let : Group.IsPerfect G := h.isPerfect Nat.prime_two
  let π := e.toMonoidHom.comp (QuotientGroup.mk' (solubleRadical G))
  have hπ : Function.Surjective π :=
    e.surjective.comp (QuotientGroup.mk'_surjective (solubleRadical G))
  have hker : π.ker = solubleRadical G := by
    exact (MonoidHom.ker_mulEquiv_comp (QuotientGroup.mk' (solubleRadical G)) e).trans
      (QuotientGroup.ker_mk' (solubleRadical G))
  have hbinary : IsPGroup 2 π.ker := by
    rw [hker, h.radical_eq_pCore Nat.prime_two]
    exact pCore_isPGroup
  exact OddPSLTwoCentralObstruction.not_productOrderCondition F hodd hcard
    π hπ hbinary (by simpa only [hker] using hcentral) w h.condition

end Kourovka2135
