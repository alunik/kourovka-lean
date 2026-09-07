import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[793, 792, 4, 4, 4, 709, 805, 804, 704, 769, 768, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 12, 12, 1, 16, 16, 1, 16, 16, 1, 12, 12, 1, 32, 32, 1, 32, 32, 1, 12, 12, 1, 32, 32, 1, 32, 32, 1, 12, 12, 1, 16, 16, 1, 16, 16, 1, 12, 12, 1, 32, 32, 1, 32, 32, 1, 12, 12, 1, 32, 32, 1, 32, 32, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 16, 16, 1, 16, 16, 1, 16, 16]

theorem obstructionChunk017 (code : Fin 19683)
    (_hlo : 2176 ≤ code.val) (hhi : code.val < 2304) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (2176 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 2176, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 2176 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
