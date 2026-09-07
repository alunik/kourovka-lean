import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[1098, 1, 12, 12, 1, 679, 694, 1, 675, 690, 1, 12, 12, 1, 1104, 1117, 1, 1117, 1104, 1, 12, 12, 1, 1088, 1101, 1, 1101, 1088, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 1000, 1003, 1, 661, 644, 1, 657, 640, 1, 709, 704, 1, 1000, 1003, 1, 1200, 1200, 1, 757, 752, 1, 1164, 1164, 1, 1000, 1003, 1, 1003, 1000, 1, 679, 694, 1, 675, 690, 1, 715, 718, 1, 1003, 1000, 1, 1200, 1200, 1, 763, 766, 1, 1164, 1164, 1, 1003, 1000, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1]

theorem obstructionChunk139 (code : Fin 19683)
    (_hlo : 17792 ≤ code.val) (hhi : code.val < 17920) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (17792 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 17792, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 17792 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
