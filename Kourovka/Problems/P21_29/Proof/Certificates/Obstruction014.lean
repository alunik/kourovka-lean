import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[4, 4, 3, 769, 768, 3, 805, 804, 3, 4, 4, 3, 793, 792, 3, 829, 828, 4, 4, 4, 16, 16, 16, 16, 16, 16, 4, 4, 4, 709, 769, 768, 704, 805, 804, 4, 4, 4, 757, 793, 792, 752, 829, 828, 4, 4, 4, 16, 16, 16, 16, 16, 16, 4, 4, 4, 718, 769, 768, 715, 805, 804, 4, 4, 4, 766, 793, 792, 763, 829, 828, 3, 4, 4, 3, 16, 16, 3, 16, 16, 3, 4, 4, 3, 793, 792, 3, 829, 828, 3, 4, 4, 3, 769, 768, 3, 805, 804, 4, 4, 4, 16, 16, 16, 16, 16, 16, 4, 4, 4, 718, 793, 792, 715, 829, 828, 4, 4, 4, 766, 769, 768, 763, 805, 804, 4, 4, 4]

theorem obstructionChunk014 (code : Fin 19683)
    (_hlo : 1792 ≤ code.val) (hhi : code.val < 1920) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (1792 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 1792, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 1792 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
