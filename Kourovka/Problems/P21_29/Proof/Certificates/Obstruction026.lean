import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[16, 16, 3, 1032, 1051, 3, 1032, 1051, 3, 1032, 1051, 3, 1051, 1032, 3, 1051, 1032, 3, 1051, 1032, 16, 16, 16, 16, 16, 16, 16, 16, 16, 620, 620, 620, 640, 1156, 715, 644, 718, 1200, 632, 632, 632, 657, 1156, 763, 661, 766, 2155, 16, 16, 16, 16, 16, 16, 16, 16, 16, 622, 622, 622, 675, 704, 1156, 679, 1200, 709, 634, 634, 634, 690, 752, 1156, 694, 2155, 757, 3, 12, 12, 3, 16, 16, 3, 16, 16, 3, 12, 12, 3, 752, 763, 3, 766, 757, 3, 12, 12, 3, 704, 715, 3, 718, 709, 12, 12, 12, 16, 16, 16, 16, 16, 16, 12, 12, 12, 675, 1000, 1003, 679, 1012, 1015, 12, 12, 12, 690, 1012, 1015, 694, 1000, 1003]

theorem obstructionChunk026 (code : Fin 19683)
    (_hlo : 3328 ≤ code.val) (hhi : code.val < 3456) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (3328 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 3328, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 3328 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
