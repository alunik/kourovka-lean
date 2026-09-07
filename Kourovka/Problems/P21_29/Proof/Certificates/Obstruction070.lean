import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[1032, 1, 1081, 1032, 1, 48, 48, 1, 48, 48, 1, 48, 48, 1, 1066, 1051, 1, 1066, 1051, 1, 1066, 1051, 1, 1051, 1066, 1, 1051, 1066, 1, 1051, 1066, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 12, 12, 1, 640, 657, 1, 644, 661, 1, 12, 12, 1, 1088, 1101, 1, 1101, 1088, 1, 12, 12, 1, 1104, 1117, 1, 1117, 1104, 1, 12, 12, 1, 690, 675, 1, 694, 679, 1, 12, 12, 1, 1098, 1095, 1, 1095, 1098, 1, 12, 12, 1, 1114, 1111, 1, 1111, 1114, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1]

theorem obstructionChunk070 (code : Fin 19683)
    (_hlo : 8960 ≤ code.val) (hhi : code.val < 9088) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (8960 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 8960, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 8960 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
