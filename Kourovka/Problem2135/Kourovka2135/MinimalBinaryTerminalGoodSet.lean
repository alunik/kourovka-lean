import Kourovka2135.OddGoodSetTerminalLifting
import Kourovka2135.MinimalBinarySplitCommutatorFiber
import Kourovka2135.MinimalBinarySplitConjugation
import Kourovka2135.BinarySplitTorusGoodPair

/-! The nonspecial terminal binary kernel case of the flexible good-set
invariant. All kernel representation, fiber, and input-order corrections
are proved. The quotient generating-good-set fact is an explicit input here
and is supplied by the separate concrete split-torus generation theorem.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135

open BinarySplitTorusGoodPair

theorem minimal_binary_terminal_good_set
    {G : Type} [Group G] [Finite G] [Group.IsPerfect G]
    (N : Subgroup G) [N.Normal] (hN : IsPGroup 2 N)
    (hmin : ∀ L : Subgroup G, L.Normal → L < N → L ≤ Subgroup.center G)
    (hnonabelian : ¬ IsMulCommutative N) (hNΦ : N ≤ frattini G)
    (hnonspecial : Subgroup.center N ≠ commutator N)
    {F : Type} [Field F] [Fintype F] [CharP F 2]
    (j : SLTwo.SL2 F ≃* (G ⧸ N))
    (f : ℕ) (hcard : Fintype.card F = 2 ^ f) (hf : 3 ≤ f)
    (r : ℕ) (hr : r.Prime) (hrodd : Odd r)
    (hB : IsGeneratingGoodSet (splitOrderSet (F := F) r))
    (hne : (splitOrderSet (F := F) r).Nonempty) :
    HasOddGeneratingGoodSetOver
      (j.symm.toMonoidHom.comp (QuotientGroup.mk' N)) (splitOrderSet (F := F) r) := by
  let B : Set (G ⧸ N) := j.symm ⁻¹' splitOrderSet (F := F) r
  have hB' : IsGeneratingGoodSet B :=
    hB.preimage_of_bijective j.symm.toMonoidHom j.symm.bijective
  have hne' : B.Nonempty := by
    obtain ⟨s, hs⟩ := hne
    exact ⟨j s, by simpa only [B, Set.mem_preimage, j.symm_apply_apply] using hs⟩
  have horder : ∀ s ∈ B, orderOf s = r := by
    intro s hs
    rw [← j.symm.orderOf_eq s]
    exact orderOf_mem_splitOrderSet hs
  have hdiff : ∀ a : G, QuotientGroup.mk' N a ∈ B →
      Function.Surjective (ConjugateCommutatorCorrection.quotientDifference N a) := by
    intro a ha
    obtain ⟨u, huorder, huconj⟩ := ha
    have hu : u ≠ 1 := by
      intro h
      exact hr.ne_one (by simpa only [h, orderOf_one] using huorder.symm)
    obtain ⟨s, hs⟩ := isConj_iff.mp huconj
    apply MinimalBinarySplitConjugation.quotientDifference_surjective
      N hN hmin hnonabelian N hN hNΦ hnonspecial j f hcard (by omega) u hu s a
    simpa only [j.apply_symm_apply] using (congrArg j hs).symm
  have hresult := hasOddGeneratingGoodSetOver_of_conjugate_fibers
    N hN hNΦ (MinimalBinarySplitConjugation.center_le_ambient_center N hmin hnonabelian)
    r hrodd B hB' hne' horder hdiff
  apply hresult
  intro a b habgen n htB htorder
  obtain ⟨u, huorder, huconj⟩ := htB
  have hu : u ≠ 1 := by
    intro h
    exact hr.ne_one (by simpa only [h, orderOf_one] using huorder.symm)
  exact minimal_binary_split_conjugate_commutator_fiber
    N hN hmin hnonabelian hNΦ hnonspecial j f hcard hf a b habgen n u hu huconj.symm
    (by rw [htorder]; exact hrodd)

end Kourovka2135
