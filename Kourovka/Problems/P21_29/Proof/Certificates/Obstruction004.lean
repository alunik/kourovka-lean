import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[2, 1, 4, 4, 1, 8, 8, 1, 8, 8, 1, 4, 4, 1, 8, 8, 1, 8, 8, 1, 4, 4, 1, 8, 8, 1, 8, 8, 1, 4, 4, 1, 8, 8, 1, 8, 8, 1, 4, 4, 1, 8, 8, 1, 8, 8, 1, 4, 4, 1, 8, 8, 1, 8, 8, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 4, 4, 1, 16, 16, 1, 16, 16, 1, 4, 4, 1, 865, 832, 1, 877, 844, 1, 4, 4, 1, 883, 850, 1, 895, 862, 1, 4, 4, 1, 16, 16, 1, 16, 16, 1, 4, 4, 1, 883, 850, 1, 895, 862, 1]

theorem obstructionChunk004 (code : Fin 19683)
    (_hlo : 512 ≤ code.val) (hhi : code.val < 640) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (512 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 512, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 512 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
