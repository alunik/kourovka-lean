import Kourovka2135.FinitePermutationMovingRank
import Kourovka2135.GeneratingPairMovingRank

/-! Taking an arbitrary power can only decrease moving rank. Thus a pair
conjugate to any powers of c, not necessarily coprime powers, suffices for
the dimension-to-moving-rank lower bound at c. -/

set_option autoImplicit false
noncomputable section
universe u

namespace Kourovka2135.RepresentationMovingPowerBound

variable {k G V : Type u} [Field k] [Group G] [AddCommGroup V] [Module k V]
variable (ρ : Representation k G V)

theorem range_moving_pow_le (g : G) (n : ℕ) :
    LinearMap.range (ρ (g ^ n) - LinearMap.id) ≤
      LinearMap.range (ρ g - LinearMap.id) := by
  rintro v ⟨w, rfl⟩
  change ρ (g ^ n) w - w ∈ LinearMap.range (ρ g - LinearMap.id)
  rw [map_pow]
  exact FinitePermutationMovingRank.pow_sub_mem_range (ρ g) n w

theorem finrank_moving_pow_le [FiniteDimensional k V] (g : G) (n : ℕ) :
    Module.finrank k (LinearMap.range (ρ (g ^ n) - LinearMap.id)) ≤
      Module.finrank k (LinearMap.range (ρ g - LinearMap.id)) :=
  Submodule.finrank_mono (range_moving_pow_le ρ g n)

theorem finrank_le_twice_moving [FiniteDimensional k V]
    (a b c : G) (hgen : Subgroup.closure ({a, b} : Set G) = ⊤)
    (hfixed : ρ.invariants = ⊥) (m n : ℕ)
    (ha : IsConj a (c ^ m)) (hb : IsConj b (c ^ n)) :
    Module.finrank k V ≤ 2 * Module.finrank k (LinearMap.range (ρ c - LinearMap.id)) := by
  have he := GeneratingPairMovingRank.finrank_le_sum_moving ρ a b hgen hfixed
  rw [RepresentationMovingConjugacy.finrank_moving_eq_of_isConj ρ ha,
    RepresentationMovingConjugacy.finrank_moving_eq_of_isConj ρ hb] at he
  have hm := finrank_moving_pow_le ρ c m
  have hn := finrank_moving_pow_le ρ c n
  omega

end Kourovka2135.RepresentationMovingPowerBound
