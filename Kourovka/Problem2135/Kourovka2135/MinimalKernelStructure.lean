import Kourovka2135.MinimalNoncentral
import Kourovka2135.SolubleStructure
import Kourovka2135.ClassTwoPowers

/-! Elementary centrality and exponent facts for minimal noncentral normal p-kernels. -/

set_option autoImplicit false
universe u
namespace Kourovka2135
variable {G : Type u} [Group G]

theorem characteristic_map_le_center_of_minimal_noncentral
    (N : Subgroup G) [N.Normal]
    (hmin : ∀ M : Subgroup G, M.Normal → M < N → M ≤ Subgroup.center G)
    (K : Subgroup N) [K.Characteristic] (hK : K ≠ ⊤) :
    K.map N.subtype ≤ Subgroup.center G := by
  apply hmin _ inferInstance
  apply lt_of_le_of_ne (Subgroup.map_subtype_le K)
  intro heq
  apply hK
  apply Subgroup.map_injective N.subtype_injective
  simpa only [← MonoidHom.range_eq_map, Subgroup.range_subtype] using heq

theorem minimal_noncentral_center_le
    (N : Subgroup G) [N.Normal] (hnonabelian : ¬ IsMulCommutative N)
    (hmin : ∀ M : Subgroup G, M.Normal → M < N → M ≤ Subgroup.center G) :
    (Subgroup.center N).map N.subtype ≤ Subgroup.center G := by
  apply characteristic_map_le_center_of_minimal_noncentral N hmin
  exact fun heq => hnonabelian (Subgroup.center_eq_top_iff.mp heq)

theorem minimal_noncentral_commutator_le_center
    (N : Subgroup G) [N.Normal] [Group.IsSolvable N]
    (hmin : ∀ M : Subgroup G, M.Normal → M < N → M ≤ Subgroup.center G) :
    ⁅N, N⁆ ≤ Subgroup.center G := by
  rcases subsingleton_or_nontrivial N with hn | hn
  · let := hn
    have hcomm : commutator N = ⊥ := (commutator_eq_bot_iff N).mpr inferInstance
    rw [← Subgroup.map_subtype_commutator, hcomm, Subgroup.map_bot]
    exact bot_le
  · let := hn
    rw [← Subgroup.map_subtype_commutator]
    exact characteristic_map_le_center_of_minimal_noncentral N hmin _
      (Group.IsSolvable.commutator_lt_top_of_nontrivial N).ne

theorem minimal_noncentral_triple_commutator_eq_bot
    (N : Subgroup G) [N.Normal] [Group.IsSolvable N]
    (hmin : ∀ M : Subgroup G, M.Normal → M < N → M ≤ Subgroup.center G) :
    ⁅⁅N, N⁆, N⁆ = ⊥ := by
  apply bot_unique
  calc
    ⁅⁅N, N⁆, N⁆ ≤ ⁅Subgroup.center G, N⁆ :=
      Subgroup.commutator_mono (minimal_noncentral_commutator_le_center N hmin) le_rfl
    _ = ⊥ := Subgroup.commutator_center_left N

theorem minimal_noncentral_frattini_le_center [Finite G]
    (N : Subgroup G) [N.Normal]
    (hmin : ∀ M : Subgroup G, M.Normal → M < N → M ≤ Subgroup.center G) :
    frattini N ≤ Subgroup.center N := by
  rcases subsingleton_or_nontrivial N with hn | hn
  · let := hn
    rw [Subgroup.center_eq_top]
    exact le_top
  · let := hn
    have hne : frattini N ≠ ⊤ := by
      intro heq
      have hbot : (⊥ : Subgroup N) = ⊤ := frattini_nongenerating (by simp [heq])
      exact bot_ne_top hbot
    have hmap := characteristic_map_le_center_of_minimal_noncentral N hmin (frattini N) hne
    intro x hx
    apply Subgroup.mem_center_iff.mpr
    intro y
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp (hmap (Subgroup.mem_map_of_mem N.subtype hx)) y

theorem minimal_noncentral_quotient_center_isElementaryAbelian [Finite G]
    {p : ℕ} (hp : p.Prime) (N : Subgroup G) [N.Normal] (hN : IsPGroup p N)
    (hmin : ∀ M : Subgroup G, M.Normal → M < N → M ≤ Subgroup.center G) :
    IsElementaryAbelian p (N ⧸ Subgroup.center N) := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fact (IsPGroup p N) := ⟨hN⟩
  have hΦ := minimal_noncentral_frattini_le_center N hmin
  refine {
    toIsMulCommutative :=
      Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr
        ((commutator_le_frattini_of_isPGroup (R := N) (p := p)).trans hΦ)
    exponent_dvd_p := ?_ }
  apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
  intro x
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center N) x
  rw [← map_pow]
  exact (QuotientGroup.eq_one_iff _).mpr
    (hΦ (pth_power_mem_frattini_of_isPGroup (p := p) a))

theorem minimal_noncentral_commutator_isElementaryAbelian [Finite G]
    {p : ℕ} (hp : p.Prime) (N : Subgroup G) [N.Normal] (hN : IsPGroup p N)
    (hmin : ∀ M : Subgroup G, M.Normal → M < N → M ≤ Subgroup.center G) :
    IsElementaryAbelian p (commutator N) := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fact (IsPGroup p N) := ⟨hN⟩
  let : Group.IsNilpotent N := hN.isNilpotent
  have hD := minimal_noncentral_commutator_le_center N hmin
  rw [← Subgroup.map_subtype_commutator] at hD
  apply commutator_isElementaryAbelian_of_powers_central p
  · intro x hx
    apply Subgroup.mem_center_iff.mpr
    intro y
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp (hD (Subgroup.mem_map_of_mem N.subtype hx)) y
  · intro x
    exact minimal_noncentral_frattini_le_center N hmin
      (pth_power_mem_frattini_of_isPGroup (p := p) x)

end Kourovka2135
