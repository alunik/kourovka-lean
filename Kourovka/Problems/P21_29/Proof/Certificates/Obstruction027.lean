import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[12, 12, 12, 16, 16, 16, 16, 16, 16, 12, 12, 12, 640, 1003, 1000, 644, 1015, 1012, 12, 12, 12, 657, 1015, 1012, 661, 1003, 1000, 3, 16, 16, 3, 16, 16, 3, 16, 16, 3, 1058, 1073, 3, 1058, 1073, 3, 1058, 1073, 3, 1073, 1058, 3, 1073, 1058, 3, 1073, 1058, 16, 16, 16, 16, 16, 16, 16, 16, 16, 620, 620, 620, 675, 752, 1156, 679, 1160, 757, 632, 632, 632, 690, 704, 1156, 694, 1160, 709, 16, 16, 16, 16, 16, 16, 16, 16, 16, 622, 622, 622, 640, 1156, 763, 644, 766, 1160, 634, 634, 634, 657, 1156, 715, 661, 718, 1160, 3, 16, 16, 3, 16, 16, 3, 16, 16, 3, 1066, 1081, 3, 1066, 1081, 3, 1066, 1081, 3, 1081]

theorem obstructionChunk027 (code : Fin 19683)
    (_hlo : 3456 ≤ code.val) (hhi : code.val < 3584) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (3456 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 3456, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 3456 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
