import Kourovka2135.OddPSLTwoSplitPrimeFrattini
import Kourovka2135.OddPSLTwoCentralKernel
import Kourovka2135.OddGoodSetMinimalObstruction
import Kourovka2135.BinarySLTwoMinimalException

/-! The odd split-prime family excludes binary least exceptions with
noncentral radical. Every kernel and representation bound is discharged;
Thompson is used only for proper-subgroup solubility. -/

set_option autoImplicit false
noncomputable section
namespace Kourovka2135
open OddPSLTwoProjectiveChart

theorem OrderMinimalException.false_of_binary_odd_pslTwo_split_noncentral
    {G : Type} [Group G] [Finite G] {w : OuterWord}
    (classification : MinimalSimpleClassification.{0})
    (h : OrderMinimalException w 2 G)
    (hnoncentral : ¬ solubleRadical G ≤ Subgroup.center G)
    (F : Type) [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) (hsize : 17 ≤ Nat.card F)
    (r : ℕ) [Fact r.Prime] (hrOdd : Odd r) (hsplit : r ∣ Nat.card F - 1)
    (e : (G ⧸ solubleRadical G) ≃* Q F) : False := by
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
  have hsolv := proper_subgroups_solvable_of_equiv e
    (h.quotient_radical_proper_subgroup_isSolvable_two classification)
  have hgood := OddPSLTwoSplitPrimeFrattini.hasOddGeneratingGoodSetOver F r
    hodd hsize hrOdd hsplit hsolv (OddPSLTwoCentralKernel.kernelBound F hodd) π hπ hR hF
  apply h.no_odd_generating_good_set_over_nontrivial hnoncentral π
    (OddPSLTwoSplitPrimeFrattini.projectiveGoodSet F r) ?_ hgood
  intro hmem
  have ho := OddPSLTwoSplitPrimeFrattini.orderOf_mem_projectiveGoodSet F r hodd hrOdd hmem
  rw [orderOf_one] at ho
  exact (Fact.out : r.Prime).ne_one ho.symm

end Kourovka2135
