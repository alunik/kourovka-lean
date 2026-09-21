import Kourovka2135.MinimalBinaryNonSpecialPair

/-! A group-theoretic reduction of a binary Frattini kernel to a usable
abelian/special minimal subgroup, or to one nonspecial minimal kernel.
The central case is eliminated by the actual central-H2 obstruction.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135

open scoped IsMulCommutative

/-- Every binary Frattini kernel above SL2(2^f), f≥3, is trivial,
contains an abelian or special minimal noncentral normal subgroup,
or is itself one nonspecial nonabelian minimal noncentral subgroup. -/
theorem binary_frattini_kernel_dichotomy
    {G : Type} [Group G] [Finite G] [Group.IsPerfect G]
    (R : Subgroup G) [R.Normal] (hR : IsPGroup 2 R)
    (hRΦ : R ≤ frattini G) [IsSimpleGroup (G ⧸ R)]
    {F : Type} [Field F] [Fintype F] [CharP F 2]
    (e : SLTwo.SL2 F ≃* (G ⧸ R))
    (f : ℕ) (hcard : Fintype.card F = 2 ^ f) (hf : 3 ≤ f) :
    R = ⊥ ∨
      (∃ N : Subgroup G, N ≤ R ∧ N.Normal ∧ ¬ N ≤ Subgroup.center G ∧
        (∀ L : Subgroup G, L.Normal → L < N → L ≤ Subgroup.center G) ∧
        (IsMulCommutative N ∨ Subgroup.center N = commutator N)) ∨
      (¬ IsMulCommutative R ∧ Subgroup.center R ≠ commutator R ∧
        ∀ L : Subgroup G, L.Normal → L < R → L ≤ Subgroup.center G) := by
  by_cases hcentral : R ≤ Subgroup.center G
  · exact Or.inl (CentralPGroupH2Obstruction.binary_eq_bot R hR hcentral F f hcard hf e)
  right
  obtain ⟨N, hNR, hnormalN, hncN, hminN⟩ := exists_minimal_normal_noncentral R hcentral
  let : N.Normal := hnormalN
  by_cases habN : IsMulCommutative N
  · exact Or.inl ⟨N, hNR, hnormalN, hncN, hminN, Or.inl habN⟩
  by_cases hsN : Subgroup.center N = commutator N
  · exact Or.inl ⟨N, hNR, hnormalN, hncN, hminN, Or.inr hsN⟩
  have hN : IsPGroup 2 N := hR.of_injective (Subgroup.inclusion hNR)
    (Subgroup.inclusion_injective hNR)
  let C := MinimalConjugationModule.Centralizer N
  have hCR : C ≤ R := MinimalConjugationModule.centralizer_le N hN hminN habN R hR
  by_cases hC : C ≤ Subgroup.center G
  · right
    have hRN : R = N := MinimalBinaryConjugationMultiplicity.eq_of_centralizer_le_center
      N hN hminN habN R hR hNR hRΦ hsN e f hcard hf hC
    rw [hRN]
    exact ⟨habN, hsN, hminN⟩
  obtain ⟨M, hMC, hnormalM, hncM, hminM⟩ := exists_minimal_normal_noncentral C hC
  let : M.Normal := hnormalM
  have hMR : M ≤ R := hMC.trans hCR
  by_cases habM : IsMulCommutative M
  · exact Or.inl ⟨M, hMR, hnormalM, hncM, hminM, Or.inl habM⟩
  by_cases hsM : Subgroup.center M = commutator M
  · exact Or.inl ⟨M, hMR, hnormalM, hncM, hminM, Or.inr hsM⟩
  exact False.elim (not_commuting_minimal_binary_nonspecial_pair R hR hRΦ
    N M hNR hMR hminN hminM habN habM hsN hsM hMC e f hcard hf)

end Kourovka2135
