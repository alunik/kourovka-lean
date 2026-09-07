import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[1012, 1015, 1, 718, 715, 1, 1012, 1015, 1, 2048, 2057, 1, 1015, 1012, 1, 657, 640, 1, 661, 644, 1, 752, 757, 1, 1156, 1156, 1, 1015, 1012, 1, 704, 709, 1, 1015, 1012, 1, 2054, 2063, 3, 12, 12, 3, 48, 48, 3, 48, 48, 3, 12, 12, 3, 675, 640, 3, 679, 644, 3, 12, 12, 3, 657, 690, 3, 661, 694, 12, 12, 12, 48, 48, 48, 48, 48, 48, 12, 12, 12, 620, 620, 620, 576, 576, 576, 12, 12, 12, 596, 596, 596, 632, 632, 632, 12, 12, 12, 48, 48, 48, 48, 48, 48, 12, 12, 12, 622, 622, 622, 578, 578, 578, 12, 12, 12, 598, 598, 598, 634, 634, 634, 3, 48, 48, 3, 48, 48, 3, 48, 48]

theorem obstructionChunk125 (code : Fin 19683)
    (_hlo : 16000 ≤ code.val) (hhi : code.val < 16128) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (16000 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 16000, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 16000 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
