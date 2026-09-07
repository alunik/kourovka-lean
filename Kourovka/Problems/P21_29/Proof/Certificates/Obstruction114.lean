import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[3, 8, 8, 3, 8, 8, 3, 4, 4, 3, 8, 8, 3, 8, 8, 4, 4, 4, 8, 8, 8, 8, 8, 8, 4, 4, 4, 8, 8, 8, 8, 8, 8, 4, 4, 4, 8, 8, 8, 8, 8, 8, 4, 4, 4, 8, 8, 8, 8, 8, 8, 4, 4, 4, 8, 8, 8, 8, 8, 8, 4, 4, 4, 8, 8, 8, 8, 8, 8, 3, 4, 4, 3, 48, 48, 3, 48, 48, 3, 4, 4, 3, 1114, 1117, 3, 1117, 1114, 3, 4, 4, 3, 1098, 1101, 3, 1101, 1098, 4, 4, 4, 48, 48, 48, 48, 48, 48, 4, 4, 4, 832, 1000, 1003, 844, 988, 991, 4, 4, 4, 883, 988, 991, 895, 1000, 1003, 4, 4, 4, 48, 48]

theorem obstructionChunk114 (code : Fin 19683)
    (_hlo : 14592 ≤ code.val) (hhi : code.val < 14720) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (14592 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 14592, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 14592 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
