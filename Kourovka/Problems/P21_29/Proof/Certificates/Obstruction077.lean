import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[963, 960, 1043, 1156, 911, 1043, 896, 1160, 1095, 1160, 1043, 578, 194, 79, 1160, 206, 205, 1111, 1043, 1160, 1156, 242, 241, 598, 76, 253, 3, 911, 896, 3, 844, 895, 3, 832, 883, 3, 911, 896, 3, 1156, 1156, 3, 828, 829, 3, 911, 896, 3, 768, 769, 3, 1184, 1184, 1032, 988, 991, 1032, 1156, 896, 1032, 911, 1184, 1101, 1032, 1168, 1156, 200, 203, 620, 124, 199, 1117, 1184, 1032, 632, 248, 127, 1184, 244, 247, 1051, 991, 988, 1051, 911, 1156, 1051, 1184, 896, 1098, 1168, 1051, 1156, 202, 201, 622, 198, 115, 1114, 1051, 1184, 634, 112, 249, 1184, 246, 245, 3, 12, 12, 3, 828, 829, 3, 768, 769, 3, 12, 12, 3, 752, 763, 3, 766, 757, 3, 12, 12]

theorem obstructionChunk077 (code : Fin 19683)
    (_hlo : 9856 ≤ code.val) (hhi : code.val < 9984) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (9856 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 9856, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 9856 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
