import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[963, 644, 988, 991, 12, 12, 12, 657, 988, 991, 661, 960, 963, 12, 12, 12, 16, 16, 16, 16, 16, 16, 12, 12, 12, 675, 963, 960, 679, 991, 988, 12, 12, 12, 690, 991, 988, 694, 963, 960, 3, 16, 16, 3, 16, 16, 3, 16, 16, 3, 1024, 1043, 3, 1024, 1043, 3, 1024, 1043, 3, 1043, 1024, 3, 1043, 1024, 3, 1043, 1024, 16, 16, 16, 16, 16, 16, 16, 16, 16, 576, 576, 576, 640, 704, 1156, 644, 1160, 709, 596, 596, 596, 657, 752, 1156, 661, 1160, 757, 16, 16, 16, 16, 16, 16, 16, 16, 16, 578, 578, 578, 675, 1156, 715, 679, 718, 1160, 598, 598, 598, 690, 1156, 763, 694, 766, 1160, 3, 16, 16, 3, 16, 16, 3]

theorem obstructionChunk025 (code : Fin 19683)
    (_hlo : 3200 ≤ code.val) (hhi : code.val < 3328) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (3200 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 3200, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 3200 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
