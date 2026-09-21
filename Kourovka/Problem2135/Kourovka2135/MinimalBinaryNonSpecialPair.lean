import Kourovka2135.MinimalBinaryConjugationMultiplicity
import Kourovka2135.BinarySLTwoH1TypeUniqueness
import Kourovka2135.DoubleQuotientKernel

/-! Two commuting nonspecial minimal noncentral kernels cannot occur
above a binary SL2 quotient. The joint faithful conjugation quotient gives
an actual two-copy quotient, contradicting the actual Frattini H2 bound.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135

open scoped IsMulCommutative

/-- This exclusion uses the actual two quotient actions and the proved
prime-field uniqueness theorem; no representation-equivalence premise is assumed. -/
theorem not_commuting_minimal_binary_nonspecial_pair
    {G : Type} [Group G] [Finite G] [Group.IsPerfect G]
    (R : Subgroup G) [R.Normal] (hR : IsPGroup 2 R)
    (hRΦ : R ≤ frattini G) [IsSimpleGroup (G ⧸ R)]
    (N M : Subgroup G) [N.Normal] [M.Normal] (hNR : N ≤ R) (hMR : M ≤ R)
    (hminN : ∀ L : Subgroup G, L.Normal → L < N → L ≤ Subgroup.center G)
    (hminM : ∀ L : Subgroup G, L.Normal → L < M → L ≤ Subgroup.center G)
    (hnabN : ¬ IsMulCommutative N) (hnabM : ¬ IsMulCommutative M)
    (hnsN : Subgroup.center N ≠ commutator N)
    (hnsM : Subgroup.center M ≠ commutator M)
    (hMN : M ≤ Subgroup.centralizer (N : Set G))
    {F : Type} [Field F] [Fintype F] [CharP F 2]
    (e : SLTwo.SL2 F ≃* (G ⧸ R))
    (f : ℕ) (hcard : Fintype.card F = 2 ^ f) (hf : 3 ≤ f) : False := by
  let C := MinimalConjugationModule.Centralizer N
  let D := MinimalConjugationModule.Centralizer M
  have hN : IsPGroup 2 N := hR.of_injective (Subgroup.inclusion hNR)
    (Subgroup.inclusion_injective hNR)
  have hM : IsPGroup 2 M := hR.of_injective (Subgroup.inclusion hMR)
    (Subgroup.inclusion_injective hMR)
  have hCR : C ≤ R := MinimalConjugationModule.centralizer_le N hN hminN hnabN R hR
  have hDR : D ≤ R := MinimalConjugationModule.centralizer_le M hM hminM hnabM R hR
  have hND : N ≤ D := by
    intro n hn
    apply Subgroup.mem_centralizer_iff.mpr
    intro m hm
    exact (Subgroup.mem_centralizer_iff.mp (hMN hm) n hn).symm
  let : IsElementaryAbelian 2 (N ⧸ Subgroup.center N) :=
    minimal_noncentral_quotient_center_isElementaryAbelian Nat.prime_two N hN hminN
  let : IsElementaryAbelian 2 (M ⧸ Subgroup.center M) :=
    minimal_noncentral_quotient_center_isElementaryAbelian Nat.prime_two M hM hminM
  let : IsElementaryAbelian 2 (NestedNormalExtension.kernel C R) :=
    MinimalConjugationModule.kernel_isElementaryAbelian N hN hminN hnabN R hR
  let : IsElementaryAbelian 2 (NestedNormalExtension.kernel D R) :=
    MinimalConjugationModule.kernel_isElementaryAbelian M hM hminM hnabM R hR
  let : IsElementaryAbelian 2 (NestedNormalExtension.kernel (C ⊓ D) R) :=
    DoubleQuotientKernel.kernel_isElementaryAbelian 2 C D R
  let ρN := minimalCenterRepresentation N hN hminN R hR
  let ρM := minimalCenterRepresentation M hM hminM R hR
  let : Representation.IsIrreducible ρN :=
    minimal_quotient_center_representation_irreducible N hminN 2 hN hnabN R hR
  let : Representation.IsIrreducible ρM :=
    minimal_quotient_center_representation_irreducible M hminM 2 hM hnabM R hR
  have hH1N := minimal_binary_h1_finrank_ne_zero_of_center_ne_commutator
    N hN hminN R hR hnabN hRΦ hnsN
  have hH1M := minimal_binary_h1_finrank_ne_zero_of_center_ne_commutator
    M hM hminM R hR hnabM hRΦ hnsM
  let a := MinimalBinaryConjugationMultiplicity.equiv
    N hN hminN hnabN R hR hNR hRΦ hnsN e f hcard hf
  let b := (MinimalBinaryConjugationMultiplicity.equiv
    M hM hminM hnabM R hR hMR hRΦ hnsM e f hcard hf).trans
      (BinarySLTwoH1TypeUniqueness.groupEquiv ρM ρN e f hcard (by omega) hH1M hH1N)
  let τ := DoubleQuotientKernel.representation 2 (C ⊓ D) R (inf_le_left.trans hCR)
  let l := DoubleQuotientKernel.kernelIntertwiner 2 (C ⊓ D) C R
    inf_le_left (inf_le_left.trans hCR) hCR
  let r := DoubleQuotientKernel.kernelIntertwiner 2 (C ⊓ D) D R
    inf_le_right (inf_le_left.trans hCR) hDR
  let j : τ.IntertwiningMap (ρN.prod ρN) :=
    (a.toIntertwiningMap.comp l).prod (b.toIntertwiningMap.comp r)
  have hj : Function.Surjective j := by
    intro y
    obtain ⟨x, hx⟩ := DoubleQuotientKernel.jointIntertwiner_surjective 2 C D R hCR hDR
      N M hNR hMR hND hMN
      (MinimalBinaryConjugationMultiplicity.images_eq
        N hN hminN hnabN R hR hNR hRΦ hnsN e f hcard hf)
      (MinimalBinaryConjugationMultiplicity.images_eq
        M hM hminM hnabM R hR hMR hRΦ hnsM e f hcard hf)
      (a.symm y.1, b.symm y.2)
    refine ⟨x, Prod.ext ?_ ?_⟩
    · change a (l x) = y.1
      have hleft : l x = a.symm y.1 := congrArg Prod.fst hx
      rw [hleft, a.apply_symm_apply]
    · change b (r x) = y.2
      have hright : r x = b.symm y.2 := congrArg Prod.snd hx
      rw [hright, b.apply_symm_apply]
  let S := NestedNormalExtension.extension (C ⊓ D) R (inf_le_left.trans hCR)
  have hcompat : AbelianExtensionCocycle.CompatibleAction S τ :=
    AbelianExtensionRepresentation.compatibleAction S 2
  have hΦ : S.inl.range ≤ frattini (G ⧸ (C ⊓ D)) := by
    rw [show S.inl.range = NestedNormalExtension.kernel (C ⊓ D) R from
      NestedNormalExtension.extension_inl_range (C ⊓ D) R (inf_le_left.trans hCR)]
    exact NestedNormalExtension.kernel_le_frattini (C ⊓ D) R hRΦ
  have hH2 := BinarySLTwoGroupEquivCohomology.finrank_H2_le_endDegree_of_finrank_H1_ne_zero
    ρN e f hcard hf hH1N
  exact FrattiniCohomologyMultiplicity.not_surjective_two_copies_of_H2_le_end
    τ ρN S hcompat hΦ hH2 j hj

end Kourovka2135
