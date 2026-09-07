import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[752, 1, 1168, 1168, 1, 991, 988, 1, 709, 704, 1, 991, 988, 1, 2002, 2035, 3, 12, 12, 3, 48, 48, 3, 48, 48, 3, 12, 12, 3, 644, 679, 3, 640, 675, 3, 12, 12, 3, 694, 661, 3, 690, 657, 12, 12, 12, 48, 48, 48, 48, 48, 48, 12, 12, 12, 632, 632, 632, 596, 596, 596, 12, 12, 12, 576, 576, 576, 620, 620, 620, 12, 12, 12, 48, 48, 48, 48, 48, 48, 12, 12, 12, 634, 634, 634, 598, 598, 598, 12, 12, 12, 578, 578, 578, 622, 622, 622, 3, 48, 48, 3, 48, 48, 3, 48, 48, 3, 804, 805, 3, 644, 679, 3, 640, 675, 3, 792, 793, 3, 694, 661, 3, 690, 657, 48, 48, 48, 48]

theorem obstructionChunk091 (code : Fin 19683)
    (_hlo : 11648 ≤ code.val) (hhi : code.val < 11776) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (11648 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 11648, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 11648 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
