import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[16, 16, 16, 16, 16, 16, 12, 12, 12, 644, 1000, 1003, 640, 1012, 1015, 12, 12, 12, 661, 1012, 1015, 657, 1000, 1003, 12, 12, 12, 16, 16, 16, 16, 16, 16, 12, 12, 12, 679, 1003, 1000, 675, 1015, 1012, 12, 12, 12, 694, 1015, 1012, 690, 1003, 1000, 3, 16, 16, 3, 16, 16, 3, 16, 16, 3, 1032, 1051, 3, 1032, 1051, 3, 1032, 1051, 3, 1051, 1032, 3, 1051, 1032, 3, 1051, 1032, 16, 16, 16, 16, 16, 16, 16, 16, 16, 596, 596, 596, 644, 1164, 704, 640, 709, 1200, 576, 576, 576, 661, 1164, 752, 657, 757, 1772, 16, 16, 16, 16, 16, 16, 16, 16, 16, 598, 598, 598, 679, 715, 1164, 675, 1200, 718, 578, 578, 578, 694, 763]

theorem obstructionChunk042 (code : Fin 19683)
    (_hlo : 5376 ≤ code.val) (hhi : code.val < 5504) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (5376 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 5376, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 5376 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
