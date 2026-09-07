import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[16, 634, 634, 634, 661, 1200, 718, 657, 715, 1200, 622, 622, 622, 644, 1957, 766, 640, 763, 2269, 16, 16, 16, 16, 16, 16, 16, 16, 16, 632, 632, 632, 694, 709, 1200, 690, 1200, 704, 620, 620, 620, 679, 757, 1956, 675, 2266, 752, 3, 12, 12, 3, 16, 16, 3, 16, 16, 3, 12, 12, 3, 757, 766, 3, 763, 752, 3, 12, 12, 3, 709, 718, 3, 715, 704, 12, 12, 12, 16, 16, 16, 16, 16, 16, 12, 12, 12, 694, 960, 963, 690, 988, 991, 12, 12, 12, 679, 988, 991, 675, 960, 963, 12, 12, 12, 16, 16, 16, 16, 16, 16, 12, 12, 12, 661, 963, 960, 657, 991, 988, 12, 12, 12, 644, 991, 988, 640, 963, 960, 3]

theorem obstructionChunk049 (code : Fin 19683)
    (_hlo : 6272 ≤ code.val) (hhi : code.val < 6400) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (6272 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 6272, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 6272 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
