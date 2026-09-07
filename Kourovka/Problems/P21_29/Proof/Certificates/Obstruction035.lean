import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[2, 2, 1, 16, 16, 1, 16, 16, 1, 16, 16, 1, 32, 32, 1, 32, 32, 1, 32, 32, 1, 32, 32, 1, 32, 32, 1, 32, 32, 1, 16, 16, 1, 16, 16, 1, 16, 16, 1, 32, 32, 1, 32, 32, 1, 32, 32, 1, 32, 32, 1, 32, 32, 1, 32, 32, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 16, 16, 1, 16, 16, 1, 16, 16, 1, 32, 32, 1, 32, 32, 1, 32, 32, 1, 32, 32, 1, 32, 32, 1, 32, 32, 1, 16, 16, 1, 16, 16, 1, 16, 16, 1, 32, 32, 1, 32, 32, 1, 32, 32]

theorem obstructionChunk035 (code : Fin 19683)
    (_hlo : 4480 ≤ code.val) (hhi : code.val < 4608) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (4480 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 4480, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 4480 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
