import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[3, 1111, 1104, 4, 4, 4, 634, 634, 634, 622, 622, 622, 4, 4, 4, 718, 1168, 877, 715, 1168, 865, 4, 4, 4, 766, 862, 1184, 763, 850, 1184, 4, 4, 4, 632, 632, 632, 620, 620, 620, 4, 4, 4, 709, 862, 1168, 704, 850, 1168, 4, 4, 4, 757, 1184, 877, 752, 1184, 865, 3, 4, 4, 3, 8, 8, 3, 8, 8, 3, 4, 4, 3, 8, 8, 3, 8, 8, 3, 4, 4, 3, 8, 8, 3, 8, 8, 4, 4, 4, 8, 8, 8, 8, 8, 8, 4, 4, 4, 8, 8, 8, 8, 8, 8, 4, 4, 4, 8, 8, 8, 8, 8, 8, 4, 4, 4, 8, 8, 8, 8, 8, 8, 4, 4, 4, 8, 8, 8, 8, 8]

theorem obstructionChunk066 (code : Fin 19683)
    (_hlo : 8448 ≤ code.val) (hhi : code.val < 8576) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (8448 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 8448, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 8448 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
