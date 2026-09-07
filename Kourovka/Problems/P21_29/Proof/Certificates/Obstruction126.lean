import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[3, 804, 805, 3, 675, 640, 3, 679, 644, 3, 792, 793, 3, 657, 690, 3, 661, 694, 48, 48, 48, 48, 48, 48, 48, 48, 48, 1104, 804, 805, 865, 1104, 1156, 877, 1160, 1104, 1088, 792, 793, 850, 1088, 1156, 862, 1160, 1088, 48, 48, 48, 48, 48, 48, 48, 48, 48, 1111, 804, 805, 850, 1156, 1111, 862, 1111, 1160, 1095, 792, 793, 865, 1156, 1095, 877, 1095, 1160, 3, 48, 48, 3, 48, 48, 3, 48, 48, 3, 792, 793, 3, 675, 640, 3, 679, 644, 3, 804, 805, 3, 657, 690, 3, 661, 694, 48, 48, 48, 48, 48, 48, 48, 48, 48, 1117, 792, 793, 877, 1156, 1117, 865, 1117, 1784, 1101, 804, 805, 862, 1156, 1101, 850, 1101, 1984, 48, 48]

theorem obstructionChunk126 (code : Fin 19683)
    (_hlo : 16128 ≤ code.val) (hhi : code.val < 16256) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (16128 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 16128, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 16128 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
