import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[4, 4, 766, 877, 1168, 763, 865, 1168, 4, 4, 4, 718, 1750, 862, 715, 1861, 850, 4, 4, 4, 576, 576, 576, 596, 596, 596, 4, 4, 4, 757, 1168, 862, 752, 1168, 850, 4, 4, 4, 709, 877, 1748, 704, 865, 1870, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 12, 12, 1, 48, 48, 1, 48, 48, 1, 12, 12, 1, 1088, 1101, 1, 1101, 1088, 1, 12, 12, 1, 1104, 1117, 1, 1117, 1104, 1, 12, 12, 1, 48, 48, 1, 48, 48, 1, 12, 12, 1, 1098, 1095, 1, 1095, 1098, 1, 12, 12, 1, 1114, 1111, 1, 1111, 1114, 1, 2, 2]

theorem obstructionChunk068 (code : Fin 19683)
    (_hlo : 8704 ≤ code.val) (hhi : code.val < 8832) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (8704 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 8704, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 8704 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
