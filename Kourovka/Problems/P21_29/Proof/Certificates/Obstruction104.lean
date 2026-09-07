import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[4, 4, 1, 48, 48, 1, 48, 48, 1, 4, 4, 1, 960, 963, 1, 1012, 1015, 1, 4, 4, 1, 1012, 1015, 1, 960, 963, 1, 4, 4, 1, 48, 48, 1, 48, 48, 1, 4, 4, 1, 963, 960, 1, 1015, 1012, 1, 4, 4, 1, 1015, 1012, 1, 963, 960, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 4, 4, 1, 8, 8, 1, 8, 8, 1, 4, 4, 1, 8, 8, 1, 8, 8, 1, 4, 4, 1, 8, 8, 1, 8, 8, 1, 4, 4, 1, 8, 8, 1, 8, 8, 1, 4, 4, 1, 8, 8, 1, 8, 8, 1, 4, 4]

theorem obstructionChunk104 (code : Fin 19683)
    (_hlo : 13312 ≤ code.val) (hhi : code.val < 13440) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (13312 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 13312, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 13312 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
