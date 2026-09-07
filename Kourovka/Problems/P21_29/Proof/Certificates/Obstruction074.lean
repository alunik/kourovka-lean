import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[1156, 1156, 1, 1003, 1000, 3, 12, 12, 3, 48, 48, 3, 48, 48, 3, 12, 12, 3, 640, 675, 3, 644, 679, 3, 12, 12, 3, 690, 657, 3, 694, 661, 12, 12, 12, 48, 48, 48, 48, 48, 48, 12, 12, 12, 576, 576, 576, 620, 620, 620, 12, 12, 12, 632, 632, 632, 596, 596, 596, 12, 12, 12, 48, 48, 48, 48, 48, 48, 12, 12, 12, 578, 578, 578, 622, 622, 622, 12, 12, 12, 634, 634, 634, 598, 598, 598, 3, 48, 48, 3, 48, 48, 3, 48, 48, 3, 768, 769, 3, 640, 675, 3, 644, 679, 3, 828, 829, 3, 690, 657, 3, 694, 661, 48, 48, 48, 48, 48, 48, 48, 48, 48, 1088, 768, 769, 832, 1088, 1156]

theorem obstructionChunk074 (code : Fin 19683)
    (_hlo : 9472 ≤ code.val) (hhi : code.val < 9600) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (9472 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 9472, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 9472 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
