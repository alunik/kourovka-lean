import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[8, 8, 4, 4, 4, 8, 8, 8, 8, 8, 8, 4, 4, 4, 8, 8, 8, 8, 8, 8, 4, 4, 4, 8, 8, 8, 8, 8, 8, 4, 4, 4, 8, 8, 8, 8, 8, 8, 4, 4, 4, 8, 8, 8, 8, 8, 8, 4, 4, 4, 8, 8, 8, 8, 8, 8, 3, 4, 4, 3, 832, 883, 3, 844, 895, 3, 4, 4, 3, 1114, 1117, 3, 1117, 1114, 3, 4, 4, 3, 1098, 1101, 3, 1101, 1098, 4, 4, 4, 598, 598, 598, 578, 578, 578, 4, 4, 4, 709, 832, 1164, 704, 844, 1200, 4, 4, 4, 757, 1164, 883, 752, 1786, 895, 4, 4, 4, 596, 596, 596, 576, 576, 576, 4, 4, 4, 718, 1164, 883, 715, 1200, 895]

theorem obstructionChunk116 (code : Fin 19683)
    (_hlo : 14848 ≤ code.val) (hhi : code.val < 14976) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (14848 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 14848, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 14848 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
