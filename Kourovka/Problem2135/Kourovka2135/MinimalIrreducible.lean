import Kourovka2135.MinimalEndomorphismBound
import Mathlib.RepresentationTheory.Irreducible

/-! The center quotient as an actual irreducible representation, including
its quotient-group action. This connects the elementary invariant-subspace
argument to mathlib's Schur-lemma API. -/

set_option autoImplicit false
universe u
namespace Kourovka2135
open scoped IsMulCommutative
variable {G : Type u} [Group G]
variable (N : Subgroup G) [N.Normal]
variable (hmin : ∀ H : Subgroup G, H.Normal → H < N → H ≤ Subgroup.center G)
variable (p : ℕ) [Fact p.Prime]
variable [IsElementaryAbelian p (N ⧸ Subgroup.center N)]

theorem centerQuotient_nontrivial_of_nonabelian (hnonabelian : ¬ IsMulCommutative N) :
    Nontrivial (N ⧸ Subgroup.center N) :=
  QuotientGroup.nontrivial_iff.mpr (fun h => hnonabelian (Subgroup.center_eq_top_iff.mp h))

include hmin in
theorem minimal_center_representation_irreducible
    (hnonabelian : ¬ IsMulCommutative N) :
    (normalQuotientRepresentation N (Subgroup.center N) p).IsIrreducible := by
  let : Nontrivial (N ⧸ Subgroup.center N) := centerQuotient_nontrivial_of_nonabelian N hnonabelian
  let ρ := normalQuotientRepresentation N (Subgroup.center N) p
  let : Nontrivial (Subrepresentation ρ) := ⟨⟨⊥, ⊤, by
    intro he
    have hh := congrArg Subrepresentation.toSubmodule he
    exact (bot_ne_top : (⊥ : Submodule (ZMod p) (Additive (N ⧸ Subgroup.center N))) ≠ ⊤) hh⟩⟩
  refine { eq_bot_or_eq_top := ?_ }
  intro W
  rcases minimal_centerQuotient_invariant_submodule_eq_bot_or_top N hmin p W.toSubmodule
    (fun g x hx => W.apply_mem_toSubmodule g hx) with h | h
  · exact Or.inl (Subrepresentation.toSubmodule_injective h)
  · exact Or.inr (Subrepresentation.toSubmodule_injective h)

theorem minimal_quotient_center_representation_irreducible [Finite G]
    (hN : IsPGroup p N) (hnonabelian : ¬ IsMulCommutative N)
    (R : Subgroup G) [R.Normal] (hR : IsPGroup p R) :
    (minimalCenterRepresentation N hN hmin R hR).IsIrreducible := by
  let : Nontrivial (N ⧸ Subgroup.center N) := centerQuotient_nontrivial_of_nonabelian N hnonabelian
  let σ := minimalCenterRepresentation N hN hmin R hR
  let : Nontrivial (Subrepresentation σ) := ⟨⟨⊥, ⊤, by
    intro he
    have hh := congrArg Subrepresentation.toSubmodule he
    exact (bot_ne_top : (⊥ : Submodule (ZMod p) (Additive (N ⧸ Subgroup.center N))) ≠ ⊤) hh⟩⟩
  refine { eq_bot_or_eq_top := ?_ }
  intro W
  rcases minimal_centerQuotient_invariant_submodule_eq_bot_or_top N hmin p W.toSubmodule
    (fun g x hx => W.apply_mem_toSubmodule (QuotientGroup.mk' R g) hx) with h | h
  · exact Or.inl (Subrepresentation.toSubmodule_injective h)
  · exact Or.inr (Subrepresentation.toSubmodule_injective h)

end Kourovka2135
