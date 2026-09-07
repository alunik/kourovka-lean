import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[1164, 690, 1774, 766, 3, 16, 16, 3, 16, 16, 3, 16, 16, 3, 1024, 1043, 3, 1024, 1043, 3, 1024, 1043, 3, 1043, 1024, 3, 1043, 1024, 3, 1043, 1024, 16, 16, 16, 16, 16, 16, 16, 16, 16, 632, 632, 632, 644, 715, 1200, 640, 1200, 718, 620, 620, 620, 661, 763, 1957, 657, 2256, 766, 16, 16, 16, 16, 16, 16, 16, 16, 16, 634, 634, 634, 679, 1200, 704, 675, 709, 1200, 622, 622, 622, 694, 1956, 752, 690, 757, 2263, 3, 12, 12, 3, 16, 16, 3, 16, 16, 3, 12, 12, 3, 763, 752, 3, 757, 766, 3, 12, 12, 3, 715, 704, 3, 709, 718, 12, 12, 12, 16, 16, 16, 16, 16, 16, 12, 12, 12, 679, 960, 963, 675]

theorem obstructionChunk043 (code : Fin 19683)
    (_hlo : 5504 ≤ code.val) (hhi : code.val < 5632) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (5504 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 5504, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 5504 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
