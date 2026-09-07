import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[4, 1, 911, 902, 1, 905, 896, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 4, 4, 1, 8, 8, 1, 8, 8, 1, 4, 4, 1, 8, 8, 1, 8, 8, 1, 4, 4, 1, 8, 8, 1, 8, 8, 1, 4, 4, 1, 8, 8, 1, 8, 8, 1, 4, 4, 1, 8, 8, 1, 8, 8, 1, 4, 4, 1, 8, 8, 1, 8, 8, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 4, 4, 1, 928, 937, 1, 934, 943, 1, 4, 4, 1]

theorem obstructionChunk055 (code : Fin 19683)
    (_hlo : 7040 ≤ code.val) (hhi : code.val < 7168) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (7040 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 7040, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 7040 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
