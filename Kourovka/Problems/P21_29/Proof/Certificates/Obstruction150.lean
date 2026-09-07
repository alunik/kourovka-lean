import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[3, 769, 768, 3, 829, 828, 3, 12, 12, 3, 709, 718, 3, 715, 704, 3, 12, 12, 3, 757, 766, 3, 763, 752, 12, 12, 12, 928, 769, 768, 943, 829, 828, 12, 12, 12, 928, 661, 1200, 943, 657, 1200, 12, 12, 12, 928, 1981, 644, 943, 2240, 640, 12, 12, 12, 943, 769, 768, 928, 829, 828, 12, 12, 12, 943, 1200, 694, 928, 1200, 690, 12, 12, 12, 943, 679, 1980, 928, 675, 2247, 3, 928, 943, 3, 832, 883, 3, 844, 895, 3, 928, 943, 3, 769, 768, 3, 1200, 1200, 3, 928, 943, 3, 1164, 1164, 3, 829, 828, 1066, 1000, 1003, 1066, 928, 1164, 1066, 1786, 943, 1114, 1066, 1200, 598, 65, 214, 1200, 217, 218, 1098, 1774, 1066, 1164, 229]

theorem obstructionChunk150 (code : Fin 19683)
    (_hlo : 19200 ≤ code.val) (hhi : code.val < 19328) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (19200 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 19200, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 19200 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
