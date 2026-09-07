import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[3, 704, 715, 3, 718, 709, 12, 12, 12, 928, 828, 829, 943, 768, 769, 12, 12, 12, 928, 1156, 675, 943, 1168, 679, 12, 12, 12, 928, 690, 1156, 943, 694, 1945, 12, 12, 12, 943, 828, 829, 928, 768, 769, 12, 12, 12, 943, 640, 1156, 928, 644, 1168, 12, 12, 12, 943, 1156, 657, 928, 1944, 661, 3, 928, 943, 3, 883, 832, 3, 895, 844, 3, 928, 943, 3, 1156, 1156, 3, 768, 769, 3, 928, 943, 3, 828, 829, 3, 1160, 1160, 1073, 1012, 1015, 1073, 928, 1156, 1073, 1160, 943, 1088, 1160, 1073, 1156, 224, 227, 620, 236, 113, 1104, 1073, 1160, 632, 114, 211, 1160, 220, 223, 1058, 1015, 1012, 1058, 1156, 943, 1058, 928, 1160, 1095, 1058, 1160, 1156, 226]

theorem obstructionChunk078 (code : Fin 19683)
    (_hlo : 9984 ≤ code.val) (hhi : code.val < 10112) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (9984 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 9984, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 9984 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
