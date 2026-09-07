import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[911, 1104, 1058, 1160, 620, 97, 243, 1160, 252, 255, 1088, 1160, 1058, 1156, 192, 195, 632, 204, 98, 1073, 1003, 1000, 1073, 1156, 911, 1073, 896, 1160, 1111, 1160, 1073, 622, 242, 110, 1160, 254, 253, 1095, 1073, 1160, 1156, 194, 193, 634, 109, 205, 3, 911, 896, 3, 877, 862, 3, 865, 850, 3, 911, 896, 3, 1156, 1156, 3, 792, 793, 3, 911, 896, 3, 804, 805, 3, 2240, 2247, 1066, 1012, 1015, 1066, 1156, 896, 1066, 911, 2035, 1117, 1066, 1748, 1156, 248, 251, 576, 93, 247, 1101, 1996, 1066, 596, 200, 94, 1856, 196, 199, 1081, 1015, 1012, 1081, 911, 1156, 1081, 1984, 896, 1114, 1750, 1081, 1156, 250, 249, 578, 246, 82, 1098, 1081, 2047, 598, 81, 201, 1867, 198, 197, 3]

theorem obstructionChunk130 (code : Fin 19683)
    (_hlo : 16640 ≤ code.val) (hhi : code.val < 16768) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (16640 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 16640, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 16640 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
