import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[16, 16, 16, 16, 16, 4, 4, 4, 763, 828, 829, 766, 792, 793, 4, 4, 4, 715, 804, 805, 718, 768, 769, 4, 4, 4, 16, 16, 16, 16, 16, 16, 4, 4, 4, 752, 828, 829, 757, 792, 793, 4, 4, 4, 704, 804, 805, 709, 768, 769, 3, 4, 4, 3, 8, 8, 3, 8, 8, 3, 4, 4, 3, 8, 8, 3, 8, 8, 3, 4, 4, 3, 8, 8, 3, 8, 8, 4, 4, 4, 8, 8, 8, 8, 8, 8, 4, 4, 4, 8, 8, 8, 8, 8, 8, 4, 4, 4, 8, 8, 8, 8, 8, 8, 4, 4, 4, 8, 8, 8, 8, 8, 8, 4, 4, 4, 8, 8, 8, 8, 8, 8, 4, 4, 4, 8, 8, 8]

theorem obstructionChunk011 (code : Fin 19683)
    (_hlo : 1408 ≤ code.val) (hhi : code.val < 1536) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (1408 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 1408, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 1408 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
