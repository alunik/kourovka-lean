import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[1101, 1168, 1117, 793, 792, 865, 1164, 1117, 877, 1117, 2152, 3, 48, 48, 3, 48, 48, 3, 48, 48, 3, 793, 792, 3, 694, 661, 3, 690, 657, 3, 805, 804, 3, 644, 679, 3, 640, 675, 48, 48, 48, 48, 48, 48, 48, 48, 48, 1095, 793, 792, 877, 1168, 1095, 865, 1095, 1168, 1111, 805, 804, 862, 1774, 1111, 850, 1111, 1909, 48, 48, 48, 48, 48, 48, 48, 48, 48, 1088, 793, 792, 862, 1088, 1168, 850, 1168, 1088, 1104, 805, 804, 877, 1104, 1772, 865, 1918, 1104, 3, 12, 12, 3, 793, 792, 3, 805, 804, 3, 12, 12, 3, 709, 718, 3, 715, 704, 3, 12, 12, 3, 757, 766, 3, 763, 752, 12, 12, 12, 896, 793, 792, 911, 805, 804]

theorem obstructionChunk098 (code : Fin 19683)
    (_hlo : 12544 ≤ code.val) (hhi : code.val < 12672) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (12544 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 12544, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 12544 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
