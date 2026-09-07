import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[679, 2210, 718, 675, 715, 1362, 16, 16, 16, 16, 16, 16, 16, 16, 16, 596, 596, 596, 661, 757, 2140, 657, 2086, 752, 576, 576, 576, 644, 709, 2225, 640, 1363, 704, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 4, 4, 1, 8, 8, 1, 8, 8, 1, 4, 4, 1, 8, 8, 1, 8, 8, 1, 4, 4, 1, 8, 8, 1, 8, 8, 1, 4, 4, 1, 8, 8, 1, 8, 8, 1, 4, 4, 1, 8, 8, 1, 8, 8, 1, 4, 4, 1, 8, 8, 1, 8, 8, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2]

theorem obstructionChunk051 (code : Fin 19683)
    (_hlo : 6528 ≤ code.val) (hhi : code.val < 6656) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (6528 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 6528, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 6528 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
