import Kourovka2135.OddPSLTwoTorusMovingRank
import Kourovka2135.OddPSLTwoCohomologyWeight
import Kourovka2135.PerfectIrreducibleCohomology
import Kourovka2135.GeneratingPairMovingRank
import Kourovka2135.RepresentationCohomologyAlternative

/-! The binary correction alternative for generating classes in odd PSL2.
For field cardinality at least seventeen, a root-character torus orbit has
dimension at least eight. An actual generating pair conjugate to coprime
powers of its output then gives moving rank at least four. All module bounds
are derived from the actual action; the generating pair is explicit data.
-/

set_option autoImplicit false
noncomputable section
universe u

namespace Kourovka2135.OddPSLTwoGeneratingClassBound
open OddPSLTwoProjectiveChart OddPSLTwoPermutationHeart
open RepresentationCohomologyAlternative

variable (F k : Type u) [Field F] [Fintype F] [Field k] [CharP k 2] [IsAlgClosed k]
variable [Group.IsPerfect (Q F)]
variable {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
variable (ρ : Representation k (Q F) V) [ρ.IsIrreducible]

/-- The actual half-field bound on the support of ordinary H1. -/
theorem half_field_le_finrank_of_nontrivial_H1 (hodd : Odd (Fintype.card F))
    [Nontrivial (groupCohomology (Rep.of ρ) 1)] :
    (Fintype.card F - 1) / 2 ≤ Module.finrank k V := by
  have hglobal := PerfectIrreducibleCohomology.invariants_eq_bot_of_nontrivial_H1 ρ
  obtain ⟨χ, v, hχ, hv, he⟩ :=
    OddPSLTwoCohomologyWeight.exists_nontrivial_character F k hodd ρ hglobal
  have hcard : (Fintype.card F : k) ≠ 0 := by
    rw [card_field_cast F k hodd]
    exact one_ne_zero
  exact OddPSLTwoTorusMovingRank.half_field_le_finrank F ρ χ v hodd hcard hχ hv he

/-- Generating conjugate-power inputs supply the entire closed-field
cohomology/moving-rank alternative needed for binary correction. -/
theorem alternative_of_generating_pair (hodd : Odd (Fintype.card F))
    (hsize : 17 ≤ Fintype.card F) (a b c : Q F)
    (hgen : Subgroup.closure ({a, b} : Set (Q F)) = ⊤)
    (m n : ℕ) (hm : m.Coprime (orderOf c)) (hn : n.Coprime (orderOf c))
    (ha : IsConj a (c ^ m)) (hb : IsConj b (c ^ n)) : Alternative ρ c := by
  by_cases hz : Module.finrank k (groupCohomology (Rep.of ρ) 1) = 0
  · exact Or.inl hz
  let : Nontrivial (groupCohomology (Rep.of ρ) 1) :=
    Module.nontrivial_of_finrank_pos (Nat.pos_of_ne_zero hz)
  have hglobal := PerfectIrreducibleCohomology.invariants_eq_bot_of_nontrivial_H1 ρ
  have hdim := half_field_le_finrank_of_nontrivial_H1 F k ρ hodd
  have hrank := GeneratingPairMovingRank.finrank_le_twice_moving
    ρ a b hgen hglobal c m n hm hn ha hb
  refine Or.inr ⟨OddPSLTwoFirstCohomology.finrank_H1_le_one F k hodd ρ hglobal, ?_⟩
  omega

end Kourovka2135.OddPSLTwoGeneratingClassBound
