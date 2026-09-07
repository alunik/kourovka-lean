import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[8, 8, 4, 4, 4, 8, 8, 8, 8, 8, 8, 4, 4, 4, 8, 8, 8, 8, 8, 8, 4, 4, 4, 8, 8, 8, 8, 8, 8, 3, 4, 4, 3, 16, 16, 3, 16, 16, 3, 4, 4, 3, 768, 769, 3, 804, 805, 3, 4, 4, 3, 792, 793, 3, 828, 829, 4, 4, 4, 16, 16, 16, 16, 16, 16, 4, 4, 4, 704, 768, 769, 709, 804, 805, 4, 4, 4, 752, 792, 793, 757, 828, 829, 4, 4, 4, 16, 16, 16, 16, 16, 16, 4, 4, 4, 715, 768, 769, 718, 804, 805, 4, 4, 4, 763, 792, 793, 766, 828, 829, 3, 4, 4, 3, 16, 16, 3, 16, 16, 3, 4, 4, 3, 792, 793, 3, 828, 829]

theorem obstructionChunk008 (code : Fin 19683)
    (_hlo : 1024 ≤ code.val) (hhi : code.val < 1152) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (1024 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 1024, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 1024 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
