import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[8, 4, 4, 4, 8, 8, 8, 8, 8, 8, 3, 4, 4, 3, 865, 850, 3, 877, 862, 3, 4, 4, 3, 1098, 1101, 3, 1101, 1098, 3, 4, 4, 3, 1114, 1117, 3, 1117, 1114, 4, 4, 4, 634, 634, 634, 622, 622, 622, 4, 4, 4, 757, 865, 1164, 752, 877, 1168, 4, 4, 4, 709, 1164, 850, 704, 2152, 862, 4, 4, 4, 632, 632, 632, 620, 620, 620, 4, 4, 4, 766, 1164, 850, 763, 1168, 862, 4, 4, 4, 718, 865, 1164, 715, 877, 2152, 3, 4, 4, 3, 877, 862, 3, 865, 850, 3, 4, 4, 3, 1088, 1095, 3, 1095, 1088, 3, 4, 4, 3, 1104, 1111, 3, 1111, 1104, 4, 4, 4, 578, 578, 578, 598, 598, 598, 4]

theorem obstructionChunk067 (code : Fin 19683)
    (_hlo : 8576 ≤ code.val) (hhi : code.val < 8704) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (8576 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 8576, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 8576 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
