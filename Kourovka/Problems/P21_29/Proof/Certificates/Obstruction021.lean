import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 12, 12, 1, 16, 16, 1, 16, 16, 1, 12, 12, 1, 1000, 1003, 1, 1012, 1015, 1, 12, 12, 1, 1012, 1015, 1, 1000, 1003, 1, 12, 12, 1, 16, 16, 1, 16, 16, 1, 12, 12, 1, 1003, 1000, 1, 1015, 1012, 1, 12, 12, 1, 1015, 1012, 1, 1003, 1000, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 16, 16, 1, 16, 16, 1, 16, 16, 1, 752, 757, 1, 865, 832, 1, 877, 844, 1, 704, 709, 1, 883, 850, 1, 895, 862, 1, 16, 16, 1, 16, 16, 1, 16]

theorem obstructionChunk021 (code : Fin 19683)
    (_hlo : 2688 ≤ code.val) (hhi : code.val < 2816) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (2688 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 2688, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 2688 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
