import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 12, 12, 1, 16, 16, 1, 16, 16, 1, 12, 12, 1, 960, 963, 1, 988, 991, 1, 12, 12, 1, 988, 991, 1, 960, 963, 1, 12, 12, 1, 16, 16, 1, 16, 16, 1, 12, 12, 1, 963, 960, 1, 991, 988, 1, 12, 12, 1, 991, 988, 1, 963, 960, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 16, 16, 1, 16, 16, 1, 16, 16, 1, 757, 752, 1, 865, 832, 1, 877, 844, 1, 709, 704, 1, 883, 850]

theorem obstructionChunk038 (code : Fin 19683)
    (_hlo : 4864 ≤ code.val) (hhi : code.val < 4992) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (4864 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 4864, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 4864 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
