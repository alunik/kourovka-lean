import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[4, 4, 1, 865, 832, 1, 877, 844, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 4, 4, 1, 16, 16, 1, 16, 16, 1, 4, 4, 1, 877, 844, 1, 865, 832, 1, 4, 4, 1, 895, 862, 1, 883, 850, 1, 4, 4, 1, 16, 16, 1, 16, 16, 1, 4, 4, 1, 895, 862, 1, 883, 850, 1, 4, 4, 1, 877, 844, 1, 865, 832, 3, 4, 4, 3, 8, 8, 3, 8, 8, 3, 4, 4, 3, 8, 8, 3, 8, 8, 3, 4, 4, 3, 8, 8, 3, 8, 8, 4, 4, 4, 8, 8, 8, 8, 8, 8, 4, 4, 4]

theorem obstructionChunk005 (code : Fin 19683)
    (_hlo : 640 ≤ code.val) (hhi : code.val < 768) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (640 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 640, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 640 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
