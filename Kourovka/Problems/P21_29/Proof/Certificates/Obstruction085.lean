import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[768, 1032, 1000, 1003, 1032, 937, 1156, 1032, 1945, 934, 1088, 1032, 1168, 578, 72, 234, 1168, 229, 230, 1104, 1957, 1032, 1156, 217, 218, 598, 213, 75, 1051, 1003, 1000, 1051, 1156, 934, 1051, 937, 1944, 1095, 1168, 1051, 576, 235, 71, 1168, 231, 228, 1111, 1051, 1956, 1156, 219, 216, 596, 68, 212, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 12, 12, 1, 48, 48, 1, 48, 48, 1, 12, 12, 1, 1098, 1095, 1, 1095, 1098, 1, 12, 12, 1, 1114, 1111, 1, 1111, 1114, 1, 12, 12, 1, 48, 48, 1, 48, 48, 1, 12, 12, 1, 1088, 1101, 1, 1101, 1088, 1]

theorem obstructionChunk085 (code : Fin 19683)
    (_hlo : 10880 ≤ code.val) (hhi : code.val < 11008) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (10880 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 10880, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 10880 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
