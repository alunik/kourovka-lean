import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[4, 4, 3, 8, 8, 3, 8, 8, 4, 4, 4, 8, 8, 8, 8, 8, 8, 4, 4, 4, 8, 8, 8, 8, 8, 8, 4, 4, 4, 8, 8, 8, 8, 8, 8, 4, 4, 4, 8, 8, 8, 8, 8, 8, 4, 4, 4, 8, 8, 8, 8, 8, 8, 4, 4, 4, 8, 8, 8, 8, 8, 8, 3, 4, 4, 3, 832, 883, 3, 844, 895, 3, 4, 4, 3, 1088, 1095, 3, 1095, 1088, 3, 4, 4, 3, 1104, 1111, 3, 1111, 1104, 4, 4, 4, 576, 576, 576, 596, 596, 596, 4, 4, 4, 704, 832, 1164, 709, 844, 1168, 4, 4, 4, 752, 1164, 883, 757, 1184, 895, 4, 4, 4, 578, 578, 578, 598, 598, 598, 4, 4, 4]

theorem obstructionChunk059 (code : Fin 19683)
    (_hlo : 7552 ≤ code.val) (hhi : code.val < 7680) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (7552 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 7552, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 7552 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
