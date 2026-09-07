import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[715, 1164, 883, 718, 1168, 895, 4, 4, 4, 763, 832, 1164, 766, 844, 1184, 3, 4, 4, 3, 844, 895, 3, 832, 883, 3, 4, 4, 3, 1098, 1101, 3, 1101, 1098, 3, 4, 4, 3, 1114, 1117, 3, 1117, 1114, 4, 4, 4, 632, 632, 632, 620, 620, 620, 4, 4, 4, 715, 844, 1168, 718, 832, 1168, 4, 4, 4, 763, 1184, 895, 766, 1184, 883, 4, 4, 4, 634, 634, 634, 622, 622, 622, 4, 4, 4, 704, 1168, 895, 709, 1168, 883, 4, 4, 4, 752, 844, 1184, 757, 832, 1184, 3, 4, 4, 3, 8, 8, 3, 8, 8, 3, 4, 4, 3, 8, 8, 3, 8, 8, 3, 4, 4, 3, 8, 8, 3, 8, 8, 4, 4, 4, 8, 8]

theorem obstructionChunk060 (code : Fin 19683)
    (_hlo : 7680 ≤ code.val) (hhi : code.val < 7808) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (7680 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 7680, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 7680 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
