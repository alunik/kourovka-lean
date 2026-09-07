import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[4, 4, 4, 766, 832, 1164, 763, 844, 1784, 3, 4, 4, 3, 844, 895, 3, 832, 883, 3, 4, 4, 3, 1104, 1111, 3, 1111, 1104, 3, 4, 4, 3, 1088, 1095, 3, 1095, 1088, 4, 4, 4, 622, 622, 622, 634, 634, 634, 4, 4, 4, 718, 844, 1200, 715, 832, 1200, 4, 4, 4, 766, 1957, 895, 763, 2250, 883, 4, 4, 4, 620, 620, 620, 632, 632, 632, 4, 4, 4, 709, 1200, 895, 704, 1200, 883, 4, 4, 4, 757, 844, 1956, 752, 832, 2253, 3, 4, 4, 3, 8, 8, 3, 8, 8, 3, 4, 4, 3, 8, 8, 3, 8, 8, 3, 4, 4, 3, 8, 8, 3, 8, 8, 4, 4, 4, 8, 8, 8, 8, 8, 8, 4, 4]

theorem obstructionChunk117 (code : Fin 19683)
    (_hlo : 14976 ≤ code.val) (hhi : code.val < 15104) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (14976 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 14976, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 14976 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
