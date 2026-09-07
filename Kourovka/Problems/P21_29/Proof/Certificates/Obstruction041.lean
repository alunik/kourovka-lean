import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 3, 16, 16, 3, 16, 16, 3, 16, 16, 3, 32, 32, 3, 32, 32, 3, 32, 32, 3, 32, 32, 3, 32, 32, 3, 32, 32, 16, 16, 16, 16, 16, 16, 16, 16, 16, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 16, 16, 16, 16, 16, 16, 16, 16, 16, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 3, 12, 12, 3, 16, 16, 3, 16, 16, 3, 12, 12, 3, 715, 704, 3, 709, 718, 3, 12, 12, 3, 763, 752, 3, 757, 766, 12, 12, 12]

theorem obstructionChunk041 (code : Fin 19683)
    (_hlo : 5248 ≤ code.val) (hhi : code.val < 5376) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (5248 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 5248, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 5248 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
