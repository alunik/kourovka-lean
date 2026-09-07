import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[694, 1, 675, 690, 1, 763, 766, 1, 960, 963, 1, 1792, 1809, 1, 715, 718, 1, 1856, 1861, 1, 960, 963, 1, 963, 960, 1, 661, 644, 1, 657, 640, 1, 757, 752, 1, 963, 960, 1, 1842, 1827, 1, 709, 704, 1, 1870, 1867, 1, 963, 960, 3, 12, 12, 3, 48, 48, 3, 48, 48, 3, 12, 12, 3, 679, 644, 3, 675, 640, 3, 12, 12, 3, 661, 694, 3, 657, 690, 12, 12, 12, 48, 48, 48, 48, 48, 48, 12, 12, 12, 596, 596, 596, 632, 632, 632, 12, 12, 12, 620, 620, 620, 576, 576, 576, 12, 12, 12, 48, 48, 48, 48, 48, 48, 12, 12, 12, 598, 598, 598, 634, 634, 634, 12, 12, 12, 622, 622, 622, 578]

theorem obstructionChunk142 (code : Fin 19683)
    (_hlo : 18176 ≤ code.val) (hhi : code.val < 18304) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (18176 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 18176, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 18176 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
