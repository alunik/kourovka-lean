import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[883, 1156, 1101, 895, 1101, 1160, 48, 48, 48, 48, 48, 48, 48, 48, 48, 1114, 805, 804, 883, 1114, 1156, 895, 1160, 1114, 1098, 793, 792, 832, 1098, 1156, 844, 1160, 1098, 3, 48, 48, 3, 48, 48, 3, 48, 48, 3, 793, 792, 3, 657, 690, 3, 661, 694, 3, 805, 804, 3, 675, 640, 3, 679, 644, 48, 48, 48, 48, 48, 48, 48, 48, 48, 1104, 793, 792, 844, 1104, 1156, 832, 1786, 1104, 1088, 805, 804, 895, 1088, 1156, 883, 2017, 1088, 48, 48, 48, 48, 48, 48, 48, 48, 48, 1111, 793, 792, 895, 1156, 1111, 883, 1111, 1784, 1095, 805, 804, 844, 1156, 1095, 832, 1095, 2002, 3, 12, 12, 3, 793, 792, 3, 805, 804, 3, 12, 12, 3, 718]

theorem obstructionChunk132 (code : Fin 19683)
    (_hlo : 16896 ≤ code.val) (hhi : code.val < 17024) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (16896 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 16896, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 16896 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
