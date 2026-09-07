import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[829, 3, 12, 12, 3, 704, 715, 3, 718, 709, 3, 12, 12, 3, 752, 763, 3, 766, 757, 12, 12, 12, 896, 768, 769, 911, 828, 829, 12, 12, 12, 896, 640, 1156, 911, 644, 1168, 12, 12, 12, 896, 1156, 657, 911, 1184, 661, 12, 12, 12, 911, 768, 769, 896, 828, 829, 12, 12, 12, 911, 1156, 675, 896, 1168, 679, 12, 12, 12, 911, 690, 1156, 896, 694, 1184, 3, 896, 911, 3, 832, 883, 3, 844, 895, 3, 896, 911, 3, 768, 769, 3, 1160, 1160, 3, 896, 911, 3, 1156, 1156, 3, 828, 829, 1024, 960, 963, 1024, 896, 1156, 1024, 1160, 911, 1088, 1024, 1160, 576, 64, 195, 1160, 204, 207, 1104, 1160, 1024, 1156, 240, 243, 596, 252, 67, 1043]

theorem obstructionChunk076 (code : Fin 19683)
    (_hlo : 9728 ≤ code.val) (hhi : code.val < 9856) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (9728 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 9728, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 9728 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
