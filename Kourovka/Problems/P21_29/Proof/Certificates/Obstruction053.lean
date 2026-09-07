import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[48, 48, 1, 4, 4, 1, 1003, 1000, 1, 991, 988, 1, 4, 4, 1, 991, 988, 1, 1003, 1000, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 4, 4, 1, 8, 8, 1, 8, 8, 1, 4, 4, 1, 8, 8, 1, 8, 8, 1, 4, 4, 1, 8, 8, 1, 8, 8, 1, 4, 4, 1, 8, 8, 1, 8, 8, 1, 4, 4, 1, 8, 8, 1, 8, 8, 1, 4, 4, 1, 8, 8, 1, 8, 8, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2]

theorem obstructionChunk053 (code : Fin 19683)
    (_hlo : 6784 ≤ code.val) (hhi : code.val < 6912) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (6784 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 6784, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 6784 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
