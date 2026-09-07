import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[937, 769, 768, 12, 12, 12, 934, 1156, 657, 937, 1168, 661, 12, 12, 12, 934, 640, 1156, 937, 644, 1944, 3, 934, 937, 3, 865, 850, 3, 877, 862, 3, 934, 937, 3, 1156, 1156, 3, 769, 768, 3, 934, 937, 3, 829, 828, 3, 1160, 1160, 1024, 1012, 1015, 1024, 1156, 937, 1024, 934, 1160, 1101, 1024, 1160, 1156, 225, 226, 622, 116, 238, 1117, 1160, 1024, 634, 209, 119, 1160, 221, 222, 1043, 1015, 1012, 1043, 934, 1156, 1043, 1160, 937, 1098, 1160, 1043, 1156, 227, 224, 620, 239, 123, 1114, 1043, 1160, 632, 120, 208, 1160, 223, 220, 3, 937, 934, 3, 877, 862, 3, 865, 850, 3, 937, 934, 3, 829, 828, 3, 1168, 1168, 3, 937, 934, 3, 1156, 1156, 3, 769]

theorem obstructionChunk084 (code : Fin 19683)
    (_hlo : 10752 ≤ code.val) (hhi : code.val < 10880) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (10752 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 10752, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 10752 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
