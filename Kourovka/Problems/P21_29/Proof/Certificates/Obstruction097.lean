import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[679, 3, 640, 675, 12, 12, 12, 48, 48, 48, 48, 48, 48, 12, 12, 12, 634, 634, 634, 598, 598, 598, 12, 12, 12, 578, 578, 578, 622, 622, 622, 12, 12, 12, 48, 48, 48, 48, 48, 48, 12, 12, 12, 632, 632, 632, 596, 596, 596, 12, 12, 12, 576, 576, 576, 620, 620, 620, 3, 48, 48, 3, 48, 48, 3, 48, 48, 3, 805, 804, 3, 694, 661, 3, 690, 657, 3, 793, 792, 3, 644, 679, 3, 640, 675, 48, 48, 48, 48, 48, 48, 48, 48, 48, 1098, 805, 804, 865, 1098, 1164, 877, 1168, 1098, 1114, 793, 792, 850, 1114, 1164, 862, 2152, 1114, 48, 48, 48, 48, 48, 48, 48, 48, 48, 1101, 805, 804, 850, 1164, 1101, 862]

theorem obstructionChunk097 (code : Fin 19683)
    (_hlo : 12416 ≤ code.val) (hhi : code.val < 12544) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (12416 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 12416, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 12416 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
