import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[928, 937, 1, 934, 943, 1, 4, 4, 1, 928, 937, 1, 934, 943, 1, 4, 4, 1, 934, 943, 1, 928, 937, 1, 4, 4, 1, 934, 943, 1, 928, 937, 1, 4, 4, 1, 934, 943, 1, 928, 937, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 4, 4, 1, 937, 928, 1, 943, 934, 1, 4, 4, 1, 937, 928, 1, 943, 934, 1, 4, 4, 1, 937, 928, 1, 943, 934, 1, 4, 4, 1, 943, 934, 1, 937, 928, 1, 4, 4, 1, 943, 934, 1, 937, 928, 1, 4, 4, 1, 943, 934, 1, 937, 928, 3, 4, 4, 3, 8, 8]

theorem obstructionChunk056 (code : Fin 19683)
    (_hlo : 7168 ≤ code.val) (hhi : code.val < 7296) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (7168 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 7168, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 7168 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
