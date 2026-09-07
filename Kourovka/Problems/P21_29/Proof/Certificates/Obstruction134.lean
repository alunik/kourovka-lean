import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[1160, 937, 1114, 1160, 1073, 1156, 211, 208, 576, 223, 90, 1098, 1073, 1160, 596, 89, 224, 1160, 239, 236, 3, 937, 934, 3, 844, 895, 3, 832, 883, 3, 937, 934, 3, 793, 792, 3, 1200, 1200, 3, 937, 934, 3, 1156, 1156, 3, 805, 804, 1066, 960, 963, 1066, 937, 1156, 1066, 2164, 934, 1104, 1066, 1200, 622, 105, 218, 1200, 213, 214, 1088, 2164, 1066, 1156, 233, 234, 634, 229, 106, 1081, 963, 960, 1081, 1156, 934, 1081, 937, 2164, 1111, 1200, 1081, 620, 219, 102, 1200, 215, 212, 1095, 1081, 2164, 1156, 235, 232, 632, 101, 228, 3, 12, 12, 3, 805, 804, 3, 793, 792, 3, 12, 12, 3, 766, 757, 3, 752, 763, 3, 12, 12, 3, 718, 709, 3, 704, 715]

theorem obstructionChunk134 (code : Fin 19683)
    (_hlo : 17152 ≤ code.val) (hhi : code.val < 17280) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (17152 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 17152, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 17152 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
