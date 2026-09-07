import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 12, 12, 1, 16, 16, 1, 16, 16, 1, 12, 12, 1, 960, 963, 1, 988, 991, 1, 12, 12, 1, 988, 991, 1, 960, 963, 1, 12, 12, 1, 16, 16, 1, 16, 16, 1, 12, 12, 1, 963, 960, 1, 991, 988, 1, 12, 12, 1, 991, 988, 1, 963, 960, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 16, 16, 1, 16, 16, 1, 16, 16, 1, 704, 709, 1, 832, 865, 1, 844, 877, 1, 752, 757, 1]

theorem obstructionChunk019 (code : Fin 19683)
    (_hlo : 2432 ≤ code.val) (hhi : code.val < 2560) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (2432 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 2432, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 2432 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
