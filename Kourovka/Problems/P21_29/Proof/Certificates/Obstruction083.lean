import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[1156, 1156, 3, 829, 828, 3, 905, 902, 3, 769, 768, 3, 1184, 1184, 1081, 988, 991, 1081, 905, 1156, 1081, 1184, 902, 1088, 1168, 1081, 1156, 201, 202, 622, 197, 121, 1104, 1081, 1184, 634, 122, 250, 1184, 245, 246, 1066, 991, 988, 1066, 1156, 902, 1066, 905, 1184, 1095, 1066, 1168, 1156, 203, 200, 620, 118, 196, 1111, 1184, 1066, 632, 251, 117, 1184, 247, 244, 3, 12, 12, 3, 829, 828, 3, 769, 768, 3, 12, 12, 3, 766, 757, 3, 752, 763, 3, 12, 12, 3, 718, 709, 3, 704, 715, 12, 12, 12, 937, 829, 828, 934, 769, 768, 12, 12, 12, 937, 690, 1156, 934, 694, 1168, 12, 12, 12, 937, 1156, 675, 934, 1945, 679, 12, 12, 12, 934, 829, 828]

theorem obstructionChunk083 (code : Fin 19683)
    (_hlo : 10624 ≤ code.val) (hhi : code.val < 10752) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (10624 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 10624, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 10624 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
