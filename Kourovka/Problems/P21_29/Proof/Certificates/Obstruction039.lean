import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[1, 895, 862, 1, 16, 16, 1, 16, 16, 1, 16, 16, 1, 763, 766, 1, 883, 850, 1, 895, 862, 1, 715, 718, 1, 865, 832, 1, 877, 844, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 16, 16, 1, 16, 16, 1, 16, 16, 1, 763, 766, 1, 877, 844, 1, 865, 832, 1, 715, 718, 1, 895, 862, 1, 883, 850, 1, 16, 16, 1, 16, 16, 1, 16, 16, 1, 757, 752, 1, 895, 862, 1, 883, 850, 1, 709, 704, 1, 877, 844, 1, 865, 832, 3, 12, 12, 3, 16, 16, 3, 16, 16, 3, 12, 12, 3, 32, 32, 3, 32]

theorem obstructionChunk039 (code : Fin 19683)
    (_hlo : 4992 ≤ code.val) (hhi : code.val < 5120) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (4992 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 4992, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 4992 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
