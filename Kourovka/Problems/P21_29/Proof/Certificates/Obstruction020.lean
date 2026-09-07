import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[850, 883, 1, 862, 895, 1, 16, 16, 1, 16, 16, 1, 16, 16, 1, 718, 715, 1, 850, 883, 1, 862, 895, 1, 766, 763, 1, 832, 865, 1, 844, 877, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 16, 16, 1, 16, 16, 1, 16, 16, 1, 718, 715, 1, 844, 877, 1, 832, 865, 1, 766, 763, 1, 862, 895, 1, 850, 883, 1, 16, 16, 1, 16, 16, 1, 16, 16, 1, 704, 709, 1, 862, 895, 1, 850, 883, 1, 752, 757, 1, 844, 877, 1, 832, 865, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2]

theorem obstructionChunk020 (code : Fin 19683)
    (_hlo : 2560 ≤ code.val) (hhi : code.val < 2688) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (2560 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 2560, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 2560 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
