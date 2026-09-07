import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[844, 1160, 1088, 1104, 828, 829, 883, 1104, 1156, 895, 1160, 1104, 48, 48, 48, 48, 48, 48, 48, 48, 48, 1095, 768, 769, 883, 1156, 1095, 895, 1095, 1160, 1111, 828, 829, 832, 1156, 1111, 844, 1111, 1160, 3, 48, 48, 3, 48, 48, 3, 48, 48, 3, 828, 829, 3, 640, 675, 3, 644, 679, 3, 768, 769, 3, 690, 657, 3, 694, 661, 48, 48, 48, 48, 48, 48, 48, 48, 48, 1101, 828, 829, 844, 1156, 1101, 832, 1101, 1168, 1117, 768, 769, 895, 1156, 1117, 883, 1117, 1957, 48, 48, 48, 48, 48, 48, 48, 48, 48, 1098, 828, 829, 895, 1098, 1156, 883, 1168, 1098, 1114, 768, 769, 844, 1114, 1156, 832, 1956, 1114, 3, 12, 12, 3, 768, 769, 3, 828]

theorem obstructionChunk075 (code : Fin 19683)
    (_hlo : 9600 ≤ code.val) (hhi : code.val < 9728) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (9600 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 9600, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 9600 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
