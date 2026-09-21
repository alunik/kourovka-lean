import Kourovka2135.CocycleGeneratorBounds
import Kourovka2135.RepresentationMovingConjugacy

/-! Moving rank from an actual generating pair. If the global fixed space
vanishes, the two moving maps jointly inject the coefficient space. When both
generators are conjugate to coprime powers of one element, that element moves
at least half the coefficient dimension. No semisimplicity is required. -/

set_option autoImplicit false
noncomputable section
universe u

namespace Kourovka2135.GeneratingPairMovingRank
open groupCohomology CocycleGeneratorBounds CocycleGeneratorEvaluation

variable {k G V : Type u} [Field k] [Group G] [AddCommGroup V] [Module k V]
variable (ρ : Representation k G V) (a b : G)

theorem fixed_eq_zero (hgen : Subgroup.closure ({a, b} : Set G) = ⊤)
    (hfixed : ρ.invariants = ⊥) (v : V) (ha : ρ a v = v) (hb : ρ b v = v) : v = 0 := by
  have hle : Subgroup.closure ({a, b} : Set G) ≤ zeroSubgroup ρ (principal ρ v) := by
    apply (Subgroup.closure_le _).mpr
    intro g hg
    rcases Set.mem_insert_iff.mp hg with hga | hgb
    · change ρ g v - v = 0
      rw [hga, ha, sub_self]
    · have he : g = b := Set.mem_singleton_iff.mp hgb
      change ρ g v - v = 0
      rw [he, hb, sub_self]
  rw [hgen] at hle
  have hz : principal ρ v = 0 := by
    apply cocycles₁_ext
    intro g
    exact hle (show g ∈ (⊤ : Subgroup G) from trivial)
  have hv : v ∈ ρ.invariants := by
    rw [← principal_ker]
    exact hz
  rw [hfixed] at hv
  exact hv

def differencePair : V →ₗ[k]
    LinearMap.range (ρ a - LinearMap.id) × LinearMap.range (ρ b - LinearMap.id) :=
  (ρ a - LinearMap.id).rangeRestrict.prod (ρ b - LinearMap.id).rangeRestrict

theorem differencePair_injective (hgen : Subgroup.closure ({a, b} : Set G) = ⊤)
    (hfixed : ρ.invariants = ⊥) : Function.Injective (differencePair ρ a b) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  have ha : ρ a v - v = 0 :=
    congrArg (fun p : LinearMap.range (ρ a - LinearMap.id) ×
      LinearMap.range (ρ b - LinearMap.id) => (p.1 : V)) hv
  have hb : ρ b v - v = 0 :=
    congrArg (fun p : LinearMap.range (ρ a - LinearMap.id) ×
      LinearMap.range (ρ b - LinearMap.id) => (p.2 : V)) hv
  exact fixed_eq_zero ρ a b hgen hfixed v (sub_eq_zero.mp ha) (sub_eq_zero.mp hb)

theorem finrank_le_sum_moving [FiniteDimensional k V]
    (hgen : Subgroup.closure ({a, b} : Set G) = ⊤) (hfixed : ρ.invariants = ⊥) :
    Module.finrank k V ≤ Module.finrank k (LinearMap.range (ρ a - LinearMap.id)) +
      Module.finrank k (LinearMap.range (ρ b - LinearMap.id)) := by
  simpa only [Module.finrank_prod] using
    LinearMap.finrank_le_finrank_of_injective
      (f := differencePair ρ a b) (differencePair_injective ρ a b hgen hfixed)

/-- Actual conjugate coprime powers turn the generating-pair bound into a
lower bound for one output's moving rank. -/
theorem finrank_le_twice_moving [FiniteDimensional k V]
    (hgen : Subgroup.closure ({a, b} : Set G) = ⊤) (hfixed : ρ.invariants = ⊥)
    (c : G) (m n : ℕ) (hm : m.Coprime (orderOf c)) (hn : n.Coprime (orderOf c))
    (ha : IsConj a (c ^ m)) (hb : IsConj b (c ^ n)) :
    Module.finrank k V ≤ 2 * Module.finrank k (LinearMap.range (ρ c - LinearMap.id)) := by
  have he := finrank_le_sum_moving ρ a b hgen hfixed
  rw [RepresentationMovingConjugacy.finrank_moving_eq_of_isConj ρ ha,
    RepresentationMovingConjugacy.finrank_moving_eq_of_isConj ρ hb,
    RepresentationMovingConjugacy.finrank_moving_pow_eq ρ c m hm,
    RepresentationMovingConjugacy.finrank_moving_pow_eq ρ c n hn,
    ← two_mul] at he
  exact he

end Kourovka2135.GeneratingPairMovingRank
