import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[32, 32, 32, 32, 32, 12, 12, 12, 32, 32, 32, 32, 32, 32, 3, 16, 16, 3, 16, 16, 3, 16, 16, 3, 32, 32, 3, 32, 32, 3, 32, 32, 3, 32, 32, 3, 32, 32, 3, 32, 32, 16, 16, 16, 16, 16, 16, 16, 16, 16, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 16, 16, 16, 16, 16, 16, 16, 16, 16, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 3, 16, 16, 3, 16, 16, 3, 16, 16, 3, 32, 32, 3, 32, 32, 3, 32, 32, 3, 32, 32, 3, 32, 32, 3, 32, 32, 16, 16, 16, 16, 16, 16]

theorem obstructionChunk029 (code : Fin 19683)
    (_hlo : 3712 ≤ code.val) (hhi : code.val < 3840) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (3712 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 3712, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 3712 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
