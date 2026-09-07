import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[634, 634, 640, 766, 1156, 644, 2152, 763, 16, 16, 16, 16, 16, 16, 16, 16, 16, 620, 620, 620, 690, 1156, 709, 694, 704, 1200, 632, 632, 632, 675, 1156, 757, 679, 752, 2152, 3, 12, 12, 3, 16, 16, 3, 16, 16, 3, 12, 12, 3, 766, 757, 3, 752, 763, 3, 12, 12, 3, 718, 709, 3, 704, 715, 12, 12, 12, 16, 16, 16, 16, 16, 16, 12, 12, 12, 690, 1000, 1003, 694, 1012, 1015, 12, 12, 12, 675, 1012, 1015, 679, 1000, 1003, 12, 12, 12, 16, 16, 16, 16, 16, 16, 12, 12, 12, 657, 1003, 1000, 661, 1015, 1012, 12, 12, 12, 640, 1015, 1012, 644, 1003, 1000, 3, 16, 16, 3, 16, 16, 3, 16, 16, 3, 1024, 1043]

theorem obstructionChunk032 (code : Fin 19683)
    (_hlo : 4096 ≤ code.val) (hhi : code.val < 4224) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (4096 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 4096, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 4096 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
