import Kourovka2135.MinimalNoncentral

/-! Nondegeneracy after quotienting the central commutator group by a proper subspace. -/

set_option autoImplicit false
universe u
namespace Kourovka2135
variable {G : Type u} [Group G]

theorem centralizer_mod_kernel_le_center_of_minimal_noncentral
    (N K : Subgroup G) [N.Normal] [K.Normal]
    (hD : ¬ ⁅N, N⁆ ≤ K)
    (hmin : ∀ M : Subgroup G, M.Normal → M < N → M ≤ Subgroup.center G) :
    N ⊓ (Subgroup.centralizer ((N.map (QuotientGroup.mk' K)) : Set (G ⧸ K))).comap
      (QuotientGroup.mk' K) ≤ Subgroup.center G := by
  let q := QuotientGroup.mk' K
  let C := N.map q
  let : C.Normal := Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective K)
  let R := N ⊓ (Subgroup.centralizer (C : Set (G ⧸ K))).comap q
  have hRne : R ≠ N := by
    intro heq
    have hC : C ≤ Subgroup.centralizer (C : Set (G ⧸ K)) := by
      rintro x ⟨n, hn, rfl⟩
      have hnR : n ∈ R := by rw [heq]; exact hn
      exact hnR.2
    have hcomm : (⁅N, N⁆).map q = ⊥ := by
      rw [Subgroup.map_commutator]
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hC
    have hle := (⁅N, N⁆).map_eq_bot_iff.mp hcomm
    exact hD (by simpa only [q, QuotientGroup.ker_mk'] using hle)
  exact hmin R inferInstance (lt_of_le_of_ne inf_le_left hRne)

end Kourovka2135
