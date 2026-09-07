import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[16, 1, 766, 763, 1, 883, 850, 1, 895, 862, 1, 718, 715, 1, 865, 832, 1, 877, 844, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 16, 16, 1, 16, 16, 1, 16, 16, 1, 766, 763, 1, 877, 844, 1, 865, 832, 1, 718, 715, 1, 895, 862, 1, 883, 850, 1, 16, 16, 1, 16, 16, 1, 16, 16, 1, 752, 757, 1, 895, 862, 1, 883, 850, 1, 704, 709, 1, 877, 844, 1, 865, 832, 3, 12, 12, 3, 16, 16, 3, 16, 16, 3, 12, 12, 3, 32, 32, 3, 32, 32, 3, 12, 12, 3, 32, 32, 3, 32, 32, 12]

theorem obstructionChunk022 (code : Fin 19683)
    (_hlo : 2816 ≤ code.val) (hhi : code.val < 2944) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (2816 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 2816, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 2816 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
