import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[1095, 1, 1095, 1098, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 1000, 1003, 1, 675, 690, 1, 679, 694, 1, 752, 757, 1, 1000, 1003, 1, 1160, 1160, 1, 704, 709, 1, 1156, 1156, 1, 1000, 1003, 1, 1003, 1000, 1, 657, 640, 1, 661, 644, 1, 766, 763, 1, 1003, 1000, 1, 1160, 1160, 1, 718, 715, 1, 1156, 1156, 1, 1003, 1000, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 1012, 1015, 1, 675, 690, 1, 679, 694, 1, 766, 763, 1, 1156, 1156, 1]

theorem obstructionChunk124 (code : Fin 19683)
    (_hlo : 15872 ≤ code.val) (hhi : code.val < 16000) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (15872 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 15872, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 15872 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
