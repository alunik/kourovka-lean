import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[1, 704, 709, 1, 1156, 1156, 1, 991, 988, 1, 752, 757, 1, 991, 988, 1, 1184, 1184, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 12, 12, 1, 690, 675, 1, 694, 679, 1, 12, 12, 1, 1088, 1101, 1, 1101, 1088, 1, 12, 12, 1, 1104, 1117, 1, 1117, 1104, 1, 12, 12, 1, 640, 657, 1, 644, 661, 1, 12, 12, 1, 1098, 1095, 1, 1095, 1098, 1, 12, 12, 1, 1114, 1111, 1, 1111, 1114, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 1012]

theorem obstructionChunk072 (code : Fin 19683)
    (_hlo : 9216 ≤ code.val) (hhi : code.val < 9344) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (9216 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 9216, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 9216 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
