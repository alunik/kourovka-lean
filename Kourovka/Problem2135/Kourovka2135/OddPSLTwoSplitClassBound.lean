import Kourovka2135.OddPSLTwoOrderThreeMovingRank
import Kourovka2135.OddPSLTwoCohomologyWeight
import Kourovka2135.PerfectIrreducibleCohomology
import Kourovka2135.RepresentationCohomologyAlternative

/-! The binary correction alternative for actual split order-three classes.

The H1-support argument extracts a nontrivial root-character vector in the
supplied representation. Two independent torus three-cycles give moving
rank four. In particular this covers the split order-three class at q=13,
without classifying irreducible modules or assuming a character table.
-/

set_option autoImplicit false
noncomputable section
universe u

namespace Kourovka2135.OddPSLTwoSplitClassBound

open OddPSLTwoProjectiveChart OddPSLTwoPermutationHeart OddPSLTwoTorusMovingRank
open RepresentationCohomologyAlternative

variable (F k : Type u) [Field F] [Fintype F] [Field k] [CharP k 2] [IsAlgClosed k]
variable [Group.IsPerfect (Q F)]
variable {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
variable (ρ : Representation k (Q F) V) [ρ.IsIrreducible]

/-- The actual split order-three class satisfies the correction alternative
for every odd field of cardinality greater than seven. -/
theorem alternative_order_three (hodd : Odd (Fintype.card F))
    (hsize : 7 < Fintype.card F) (r : Fˣ) (hr : orderOf r = 3) :
    Alternative ρ (projectiveTorusHom F r) := by
  by_cases hz : Module.finrank k (groupCohomology (Rep.of ρ) 1) = 0
  · exact Or.inl hz
  let : Nontrivial (groupCohomology (Rep.of ρ) 1) :=
    Module.nontrivial_of_finrank_pos (Nat.pos_of_ne_zero hz)
  have hglobal := PerfectIrreducibleCohomology.invariants_eq_bot_of_nontrivial_H1 ρ
  obtain ⟨χ, v, hχ, hv, he⟩ :=
    OddPSLTwoCohomologyWeight.exists_nontrivial_character F k hodd ρ hglobal
  have hcard : (Fintype.card F : k) ≠ 0 := by
    rw [card_field_cast F k hodd]
    exact one_ne_zero
  exact Or.inr ⟨OddPSLTwoFirstCohomology.finrank_H1_le_one F k hodd ρ hglobal,
    OddPSLTwoOrderThreeMovingRank.four_le_finrank_moving
      F ρ χ v hcard hχ hv he hsize r hr⟩

/-- Conjugacy transports the genuine order-three moving-rank calculation. -/
theorem alternative_of_isConj_order_three (hodd : Odd (Fintype.card F))
    (hsize : 7 < Fintype.card F) (r : Fˣ) (hr : orderOf r = 3)
    (g : Q F) (hg : IsConj g (projectiveTorusHom F r)) : Alternative ρ g := by
  rcases alternative_order_three F k ρ hodd hsize r hr with hz | ⟨h1, hmove⟩
  · exact Or.inl hz
  · refine Or.inr ⟨h1, ?_⟩
    rw [RepresentationMovingConjugacy.finrank_moving_eq_of_isConj ρ hg]
    exact hmove

end Kourovka2135.OddPSLTwoSplitClassBound
