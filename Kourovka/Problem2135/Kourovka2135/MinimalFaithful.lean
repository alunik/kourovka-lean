import Kourovka2135.MinimalIrreducible
import Mathlib.GroupTheory.Subgroup.Simple

/-! Faithfulness of the actual minimal-kernel module for a simple quotient. -/
set_option autoImplicit false
namespace Kourovka2135
open scoped IsMulCommutative

/-- A simple group acts faithfully if the dual has no fixed vectors and the
module is nonzero. No absolute irreducibility hypothesis is needed. -/
theorem representation_injective_of_simple_of_dual_invariants_eq_bot
    {S k M : Type*} [Group S] [IsSimpleGroup S] [Field k]
    [AddCommGroup M] [Module k M] [Nontrivial M]
    (ρ : Representation k S M) (hρ : ρ.dual.invariants = ⊥) :
    Function.Injective ρ := by
  apply ρ.ker_eq_bot_iff.mp
  rcases (inferInstance : ρ.ker.Normal).eq_bot_or_eq_top with hker | hker
  · exact hker
  · exfalso
    have htr (g : S) : ρ g = 1 := by
      have hg : g ∈ ρ.ker := by rw [hker]; trivial
      exact hg
    obtain ⟨ell, hell⟩ := exists_ne (0 : Module.Dual k M)
    have hm : ell ∈ ρ.dual.invariants := by
      intro g
      apply LinearMap.ext
      intro x
      change ell (ρ g⁻¹ x) = ell x
      rw [htr]
      rfl
    have hz : ell ∈ (⊥ : Submodule k (Module.Dual k M)) := hρ.le hm
    exact hell hz

theorem minimal_center_representation_injective
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (N : Subgroup G) [N.Normal] (hN : IsPGroup p N)
    (hmin : ∀ H : Subgroup G, H.Normal → H < N → H ≤ Subgroup.center G)
    (hnonabelian : ¬ IsMulCommutative N)
    (hmove : ⁅N, (⊤ : Subgroup G)⁆ = N)
    (R : Subgroup G) [R.Normal] (hR : IsPGroup p R) [IsSimpleGroup (G ⧸ R)]
    [IsElementaryAbelian p (N ⧸ Subgroup.center N)] :
    Function.Injective (minimalCenterRepresentation N hN hmin R hR) := by
  let : Nontrivial (N ⧸ Subgroup.center N) := centerQuotient_nontrivial_of_nonabelian N hnonabelian
  apply representation_injective_of_simple_of_dual_invariants_eq_bot
  apply quotientRepresentation_dual_invariants_eq_bot
  exact normal_quotient_dual_invariants_eq_bot N (Subgroup.center N) hmove p

/-- Perfectness supplies the moving-kernel premise in the minimal nonabelian case. -/
theorem minimal_center_representation_injective_of_perfect
    {G : Type*} [Group G] [Finite G] [Group.IsPerfect G] {p : ℕ} [Fact p.Prime]
    (N : Subgroup G) [N.Normal] (hN : IsPGroup p N)
    (hmin : ∀ H : Subgroup G, H.Normal → H < N → H ≤ Subgroup.center G)
    (hnonabelian : ¬ IsMulCommutative N)
    (R : Subgroup G) [R.Normal] (hR : IsPGroup p R) [IsSimpleGroup (G ⧸ R)]
    [IsElementaryAbelian p (N ⧸ Subgroup.center N)] :
    Function.Injective (minimalCenterRepresentation N hN hmin R hR) := by
  have hnc : ¬ N ≤ Subgroup.center G := by
    intro h
    apply hnonabelian
    exact ⟨⟨fun a b => Subtype.ext (Subgroup.mem_center_iff.mp (h b.property) a)⟩⟩
  exact minimal_center_representation_injective N hN hmin hnonabelian
    (commutator_eq_self_of_minimal_noncentral N hnc hmin) R hR

theorem exists_moved_vector_of_injective_representation
    {S k M : Type*} [Group S] [Semiring k] [AddCommMonoid M] [Module k M]
    (ρ : Representation k S M) (hρ : Function.Injective ρ) (s : S) (hs : s ≠ 1) :
    ∃ x : M, ρ s x ≠ x := by
  classical
  by_contra h
  push_neg at h
  apply hs
  apply hρ
  rw [map_one]
  apply LinearMap.ext
  exact h

end Kourovka2135
