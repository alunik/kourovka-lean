import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[1, 32, 32, 1, 32, 32, 1, 32, 32, 1, 32, 32, 1, 32, 32, 1, 32, 32, 1, 16, 16, 1, 16, 16, 1, 16, 16, 1, 32, 32, 1, 32, 32, 1, 32, 32, 1, 32, 32, 1, 32, 32, 1, 32, 32, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 16, 16, 1, 16, 16, 1, 16, 16, 1, 32, 32, 1, 32, 32, 1, 32, 32, 1, 32, 32, 1, 32, 32, 1, 32, 32, 1, 16, 16, 1, 16, 16, 1, 16, 16, 1, 32, 32, 1, 32, 32, 1, 32, 32, 1, 32, 32, 1, 32, 32, 1, 32, 32, 1, 2]

theorem obstructionChunk018 (code : Fin 19683)
    (_hlo : 2304 ≤ code.val) (hhi : code.val < 2432) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (2304 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 2304, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 2304 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
