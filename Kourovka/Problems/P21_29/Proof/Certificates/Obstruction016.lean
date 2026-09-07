import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[828, 3, 793, 792, 4, 4, 4, 16, 16, 16, 16, 16, 16, 4, 4, 4, 757, 805, 804, 752, 769, 768, 4, 4, 4, 709, 829, 828, 704, 793, 792, 4, 4, 4, 16, 16, 16, 16, 16, 16, 4, 4, 4, 766, 805, 804, 763, 769, 768, 4, 4, 4, 718, 829, 828, 715, 793, 792, 3, 4, 4, 3, 16, 16, 3, 16, 16, 3, 4, 4, 3, 829, 828, 3, 793, 792, 3, 4, 4, 3, 805, 804, 3, 769, 768, 4, 4, 4, 16, 16, 16, 16, 16, 16, 4, 4, 4, 766, 829, 828, 763, 793, 792, 4, 4, 4, 718, 805, 804, 715, 769, 768, 4, 4, 4, 16, 16, 16, 16, 16, 16, 4, 4, 4, 757, 829, 828, 752]

theorem obstructionChunk016 (code : Fin 19683)
    (_hlo : 2048 ≤ code.val) (hhi : code.val < 2176) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (2048 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 2048, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 2048 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
