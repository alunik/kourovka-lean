import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[16, 16, 16, 16, 576, 576, 576, 657, 1156, 757, 661, 752, 1748, 596, 596, 596, 640, 1156, 709, 644, 704, 2035, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 12, 12, 1, 16, 16, 1, 16, 16, 1, 12, 12, 1, 32, 32, 1, 32, 32, 1, 12, 12, 1, 32, 32, 1, 32, 32, 1, 12, 12, 1, 16, 16, 1, 16, 16, 1, 12, 12, 1, 32, 32, 1, 32, 32, 1, 12, 12, 1, 32, 32, 1, 32, 32, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1]

theorem obstructionChunk034 (code : Fin 19683)
    (_hlo : 4352 ≤ code.val) (hhi : code.val < 4480) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (4352 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 4352, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 4352 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
