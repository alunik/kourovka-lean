import Kourovka2135.ProblemBinary
import Kourovka2135.OddNoncentralComplete

/-! The remaining least-exception branch after the complete binary and odd
noncentral proofs. This reduction does not assert the unrestricted problem. -/

set_option autoImplicit false
namespace Kourovka2135

/-- Every remaining least exception is at an odd prime and has central radical.
This is a reduction to the remaining branch, not the unrestricted conclusion. -/
theorem OrderMinimalException.odd_and_radical_le_center
    (classification : MinimalSimpleClassification.{0})
    {G : Type} [Group G] [Finite G] {w : OuterWord} {p : ℕ}
    (h : OrderMinimalException w p G) (hp : p.Prime) :
    Odd p ∧ solubleRadical G ≤ Subgroup.center G := by
  have hodd : p ≠ 2 := by
    intro he
    subst p
    exact h.false_two classification
  refine ⟨hp.odd_of_ne_two hodd, ?_⟩
  by_contra hnoncentral
  exact h.false_of_odd_noncentral classification hp hodd hnoncentral

end Kourovka2135
