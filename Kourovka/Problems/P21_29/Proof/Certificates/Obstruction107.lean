import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 4, 4, 1, 896, 905, 1, 902, 911, 1, 4, 4, 1, 896, 905, 1, 902, 911, 1, 4, 4, 1, 896, 905, 1, 902, 911, 1, 4, 4, 1, 902, 911, 1, 896, 905, 1, 4, 4, 1, 902, 911, 1, 896, 905, 1, 4, 4, 1, 902, 911, 1, 896, 905, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 4, 4, 1, 905, 896, 1, 911, 902, 1, 4, 4, 1, 905, 896, 1, 911, 902, 1, 4, 4, 1, 905, 896, 1, 911, 902]

theorem obstructionChunk107 (code : Fin 19683)
    (_hlo : 13696 ≤ code.val) (hhi : code.val < 13824) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (13696 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 13696, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 13696 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
