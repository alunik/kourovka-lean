import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[1015, 1, 690, 675, 1, 694, 679, 1, 752, 757, 1, 1156, 1156, 1, 1012, 1015, 1, 704, 709, 1, 1012, 1015, 1, 1160, 1160, 1, 1015, 1012, 1, 640, 657, 1, 644, 661, 1, 766, 763, 1, 1156, 1156, 1, 1015, 1012, 1, 718, 715, 1, 1015, 1012, 1, 1160, 1160, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 1000, 1003, 1, 690, 675, 1, 694, 679, 1, 766, 763, 1, 1000, 1003, 1, 1168, 1168, 1, 718, 715, 1, 1156, 1156, 1, 1000, 1003, 1, 1003, 1000, 1, 640, 657, 1, 644, 661, 1, 752, 757, 1, 1003, 1000, 1, 1168, 1168, 1, 704, 709, 1]

theorem obstructionChunk073 (code : Fin 19683)
    (_hlo : 9344 ≤ code.val) (hhi : code.val < 9472) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (9344 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 9344, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 9344 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
