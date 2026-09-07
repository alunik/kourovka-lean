import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[32, 32, 3, 32, 32, 16, 16, 16, 16, 16, 16, 16, 16, 16, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 16, 16, 16, 16, 16, 16, 16, 16, 16, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 3, 12, 12, 3, 16, 16, 3, 16, 16, 3, 12, 12, 3, 709, 718, 3, 715, 704, 3, 12, 12, 3, 757, 766, 3, 763, 752, 12, 12, 12, 16, 16, 16, 16, 16, 16, 12, 12, 12, 661, 1000, 1003, 657, 1012, 1015, 12, 12, 12, 644, 1012, 1015, 640, 1000, 1003, 12, 12, 12, 16, 16, 16, 16, 16, 16, 12, 12, 12, 694, 1003, 1000]

theorem obstructionChunk047 (code : Fin 19683)
    (_hlo : 6016 ≤ code.val) (hhi : code.val < 6144) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (6016 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 6016, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 6016 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
