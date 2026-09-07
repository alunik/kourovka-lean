import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 48, 48, 1, 48, 48, 1, 48, 48, 1, 1066, 1051, 1, 1066, 1051, 1, 1066, 1051, 1, 1051, 1066, 1, 1051, 1066, 1, 1051, 1066, 1, 48, 48, 1, 48, 48, 1, 48, 48, 1, 1032, 1081, 1, 1032, 1081, 1, 1032, 1081, 1, 1081, 1032, 1, 1081, 1032, 1, 1081, 1032, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 12, 12, 1, 657, 640, 1, 661, 644, 1, 12, 12, 1, 1104, 1117, 1, 1117, 1104, 1, 12, 12, 1, 1088, 1101, 1, 1101, 1088, 1, 12, 12, 1, 675, 690, 1, 679, 694, 1]

theorem obstructionChunk121 (code : Fin 19683)
    (_hlo : 15488 ≤ code.val) (hhi : code.val < 15616) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (15488 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 15488, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 15488 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
