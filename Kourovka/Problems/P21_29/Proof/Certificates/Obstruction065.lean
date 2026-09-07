import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[8, 8, 8, 8, 8, 4, 4, 4, 8, 8, 8, 8, 8, 8, 4, 4, 4, 8, 8, 8, 8, 8, 8, 3, 4, 4, 3, 850, 865, 3, 862, 877, 3, 4, 4, 3, 1098, 1101, 3, 1101, 1098, 3, 4, 4, 3, 1114, 1117, 3, 1117, 1114, 4, 4, 4, 578, 578, 578, 598, 598, 598, 4, 4, 4, 709, 1164, 865, 704, 1168, 877, 4, 4, 4, 757, 850, 1164, 752, 862, 1184, 4, 4, 4, 576, 576, 576, 596, 596, 596, 4, 4, 4, 718, 850, 1164, 715, 862, 1168, 4, 4, 4, 766, 1164, 865, 763, 1184, 877, 3, 4, 4, 3, 862, 877, 3, 850, 865, 3, 4, 4, 3, 1088, 1095, 3, 1095, 1088, 3, 4, 4, 3, 1104, 1111]

theorem obstructionChunk065 (code : Fin 19683)
    (_hlo : 8320 ≤ code.val) (hhi : code.val < 8448) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (8320 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 8320, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 8320 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
