import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[704, 1, 832, 865, 1, 844, 877, 1, 757, 752, 1, 850, 883, 1, 862, 895, 1, 16, 16, 1, 16, 16, 1, 16, 16, 1, 715, 718, 1, 850, 883, 1, 862, 895, 1, 763, 766, 1, 832, 865, 1, 844, 877, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 16, 16, 1, 16, 16, 1, 16, 16, 1, 715, 718, 1, 844, 877, 1, 832, 865, 1, 763, 766, 1, 862, 895, 1, 850, 883, 1, 16, 16, 1, 16, 16, 1, 16, 16, 1, 709, 704, 1, 862, 895, 1, 850, 883, 1, 757, 752, 1, 844, 877, 1, 832, 865, 1, 2, 2, 1]

theorem obstructionChunk037 (code : Fin 19683)
    (_hlo : 4736 ≤ code.val) (hhi : code.val < 4864) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (4736 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 4736, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 4736 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
