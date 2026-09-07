import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[8, 8, 8, 8, 8, 8, 4, 4, 4, 8, 8, 8, 8, 8, 8, 4, 4, 4, 8, 8, 8, 8, 8, 8, 4, 4, 4, 8, 8, 8, 8, 8, 8, 4, 4, 4, 8, 8, 8, 8, 8, 8, 3, 4, 4, 3, 16, 16, 3, 16, 16, 3, 4, 4, 3, 32, 32, 3, 32, 32, 3, 4, 4, 3, 32, 32, 3, 32, 32, 4, 4, 4, 16, 16, 16, 16, 16, 16, 4, 4, 4, 32, 32, 32, 32, 32, 32, 4, 4, 4, 32, 32, 32, 32, 32, 32, 4, 4, 4, 16, 16, 16, 16, 16, 16, 4, 4, 4, 32, 32, 32, 32, 32, 32, 4, 4, 4, 32, 32, 32, 32, 32, 32, 3, 4, 4, 3, 16]

theorem obstructionChunk006 (code : Fin 19683)
    (_hlo : 768 ≤ code.val) (hhi : code.val < 896) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (768 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 768, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 768 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
