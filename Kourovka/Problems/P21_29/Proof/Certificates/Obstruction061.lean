import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[8, 8, 8, 8, 4, 4, 4, 8, 8, 8, 8, 8, 8, 4, 4, 4, 8, 8, 8, 8, 8, 8, 4, 4, 4, 8, 8, 8, 8, 8, 8, 4, 4, 4, 8, 8, 8, 8, 8, 8, 4, 4, 4, 8, 8, 8, 8, 8, 8, 3, 4, 4, 3, 883, 832, 3, 895, 844, 3, 4, 4, 3, 1088, 1095, 3, 1095, 1088, 3, 4, 4, 3, 1104, 1111, 3, 1111, 1104, 4, 4, 4, 632, 632, 632, 620, 620, 620, 4, 4, 4, 752, 1164, 832, 757, 1168, 844, 4, 4, 4, 704, 883, 1164, 709, 895, 2155, 4, 4, 4, 634, 634, 634, 622, 622, 622, 4, 4, 4, 763, 883, 1164, 766, 895, 1168, 4, 4, 4, 715, 1164, 832, 718]

theorem obstructionChunk061 (code : Fin 19683)
    (_hlo : 7808 ≤ code.val) (hhi : code.val < 7936) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (7808 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 7808, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 7808 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
