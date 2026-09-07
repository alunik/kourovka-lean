import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[4, 8, 8, 8, 8, 8, 8, 4, 4, 4, 8, 8, 8, 8, 8, 8, 3, 4, 4, 3, 16, 16, 3, 16, 16, 3, 4, 4, 3, 804, 805, 3, 768, 769, 3, 4, 4, 3, 828, 829, 3, 792, 793, 4, 4, 4, 16, 16, 16, 16, 16, 16, 4, 4, 4, 752, 804, 805, 757, 768, 769, 4, 4, 4, 704, 828, 829, 709, 792, 793, 4, 4, 4, 16, 16, 16, 16, 16, 16, 4, 4, 4, 763, 804, 805, 766, 768, 769, 4, 4, 4, 715, 828, 829, 718, 792, 793, 3, 4, 4, 3, 16, 16, 3, 16, 16, 3, 4, 4, 3, 828, 829, 3, 792, 793, 3, 4, 4, 3, 804, 805, 3, 768, 769, 4, 4, 4, 16]

theorem obstructionChunk010 (code : Fin 19683)
    (_hlo : 1280 ≤ code.val) (hhi : code.val < 1408) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (1280 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 1280, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 1280 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
