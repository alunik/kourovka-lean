import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[12, 12, 3, 48, 48, 3, 48, 48, 3, 12, 12, 3, 657, 690, 3, 661, 694, 3, 12, 12, 3, 675, 640, 3, 679, 644, 12, 12, 12, 48, 48, 48, 48, 48, 48, 12, 12, 12, 622, 622, 622, 578, 578, 578, 12, 12, 12, 598, 598, 598, 634, 634, 634, 12, 12, 12, 48, 48, 48, 48, 48, 48, 12, 12, 12, 620, 620, 620, 576, 576, 576, 12, 12, 12, 596, 596, 596, 632, 632, 632, 3, 48, 48, 3, 48, 48, 3, 48, 48, 3, 805, 804, 3, 657, 690, 3, 661, 694, 3, 793, 792, 3, 675, 640, 3, 679, 644, 48, 48, 48, 48, 48, 48, 48, 48, 48, 1117, 805, 804, 832, 1156, 1117, 844, 1117, 1160, 1101, 793, 792]

theorem obstructionChunk131 (code : Fin 19683)
    (_hlo : 16768 ≤ code.val) (hhi : code.val < 16896) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (16768 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 16768, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 16768 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
