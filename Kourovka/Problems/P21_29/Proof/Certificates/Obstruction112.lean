import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[865, 3, 4, 4, 3, 8, 8, 3, 8, 8, 3, 4, 4, 3, 8, 8, 3, 8, 8, 3, 4, 4, 3, 8, 8, 3, 8, 8, 4, 4, 4, 8, 8, 8, 8, 8, 8, 4, 4, 4, 8, 8, 8, 8, 8, 8, 4, 4, 4, 8, 8, 8, 8, 8, 8, 4, 4, 4, 8, 8, 8, 8, 8, 8, 4, 4, 4, 8, 8, 8, 8, 8, 8, 4, 4, 4, 8, 8, 8, 8, 8, 8, 3, 4, 4, 3, 865, 850, 3, 877, 862, 3, 4, 4, 3, 1104, 1111, 3, 1111, 1104, 3, 4, 4, 3, 1088, 1095, 3, 1095, 1088, 4, 4, 4, 620, 620, 620, 632, 632, 632, 4, 4, 4, 752, 865, 1164, 757, 877, 1945, 4]

theorem obstructionChunk112 (code : Fin 19683)
    (_hlo : 14336 ≤ code.val) (hhi : code.val < 14464) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (14336 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 14336, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 14336 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
