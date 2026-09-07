import Kourovka.Problems.P21_03.Proof.WeightedConfiguration

/-!
# Cardinality bound from a sigma-valued configuration encoding

This module packages the routine conversion from an embedding into a dependent
sum of weighted-configuration codes to the corresponding finite sum bound.
-/

open scoped BigOperators

namespace Kourovka213

universe u v

/-- An embedding into weighted-configuration codes indexed by `Fin (q + 1)`
bounds the source cardinality by the sum of the cardinalities of those codes. -/
theorem card_le_sum_weightedConfigurationCode_of_embedding
    {Site : Type u} {α : Type v}
    [Fintype Site] [DecidableEq Site] [Fintype α]
    (D s q : ℕ)
    (e : α ↪
      (Σ k : Fin (q + 1), WeightedConfigurationCode Site D s k)) :
    Fintype.card α ≤
      ∑ k ∈ Finset.range (q + 1),
        Fintype.card (WeightedConfigurationCode Site D s k) := by
  calc
    Fintype.card α ≤ Fintype.card
        (Σ k : Fin (q + 1), WeightedConfigurationCode Site D s k) :=
      Fintype.card_le_of_injective e e.injective
    _ = ∑ k : Fin (q + 1),
        Fintype.card (WeightedConfigurationCode Site D s k) :=
      Fintype.card_sigma
    _ = ∑ k ∈ Finset.range (q + 1),
        Fintype.card (WeightedConfigurationCode Site D s k) :=
      Fin.sum_univ_eq_sum_range
        (fun k : ℕ ↦ Fintype.card (WeightedConfigurationCode Site D s k))
        (q + 1)

end Kourovka213
