import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[988, 991, 12, 12, 12, 694, 988, 991, 690, 960, 963, 12, 12, 12, 16, 16, 16, 16, 16, 16, 12, 12, 12, 644, 963, 960, 640, 991, 988, 12, 12, 12, 661, 991, 988, 657, 963, 960, 3, 16, 16, 3, 16, 16, 3, 16, 16, 3, 1066, 1081, 3, 1066, 1081, 3, 1066, 1081, 3, 1081, 1066, 3, 1081, 1066, 3, 1081, 1066, 16, 16, 16, 16, 16, 16, 16, 16, 16, 632, 632, 632, 679, 1164, 752, 675, 757, 1945, 620, 620, 620, 694, 1164, 704, 690, 709, 1792, 16, 16, 16, 16, 16, 16, 16, 16, 16, 634, 634, 634, 644, 763, 1164, 640, 1944, 766, 622, 622, 622, 661, 715, 1164, 657, 1827, 718, 3, 16, 16, 3, 16, 16, 3, 16, 16]

theorem obstructionChunk044 (code : Fin 19683)
    (_hlo : 5632 ≤ code.val) (hhi : code.val < 5760) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (5632 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 5632, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 5632 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
