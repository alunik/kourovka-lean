import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 1012, 1015, 1, 644, 661, 1, 640, 657, 1, 709, 704, 1, 1164, 1164, 1, 1012, 1015, 1, 757, 752, 1, 1012, 1015, 1, 1184, 1184, 1, 1015, 1012, 1, 694, 679, 1, 690, 675, 1, 715, 718, 1, 1164, 1164, 1, 1015, 1012, 1, 763, 766, 1, 1015, 1012, 1, 1184, 1184, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 1000, 1003, 1, 644, 661, 1, 640, 657, 1, 715, 718, 1, 1000, 1003, 1, 1168, 1168, 1, 763, 766, 1, 1184, 1184, 1]

theorem obstructionChunk088 (code : Fin 19683)
    (_hlo : 11264 ≤ code.val) (hhi : code.val < 11392) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (11264 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 11264, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 11264 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
