import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[12, 12, 1, 1104, 1117, 1, 1117, 1104, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 48, 48, 1, 48, 48, 1, 48, 48, 1, 1032, 1081, 1, 1032, 1081, 1, 1032, 1081, 1, 1081, 1032, 1, 1081, 1032, 1, 1081, 1032, 1, 48, 48, 1, 48, 48, 1, 48, 48, 1, 1066, 1051, 1, 1066, 1051, 1, 1066, 1051, 1, 1051, 1066, 1, 1051, 1066, 1, 1051, 1066, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 48, 48, 1, 48, 48, 1, 48, 48, 1, 1024, 1073]

theorem obstructionChunk086 (code : Fin 19683)
    (_hlo : 11008 ≤ code.val) (hhi : code.val < 11136) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (11008 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 11008, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 11008 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
