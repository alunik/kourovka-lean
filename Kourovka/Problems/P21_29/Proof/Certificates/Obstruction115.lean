import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[48, 48, 48, 48, 4, 4, 4, 883, 1003, 1000, 895, 991, 988, 4, 4, 4, 832, 991, 988, 844, 1003, 1000, 3, 4, 4, 3, 48, 48, 3, 48, 48, 3, 4, 4, 3, 1104, 1111, 3, 1111, 1104, 3, 4, 4, 3, 1088, 1095, 3, 1095, 1088, 4, 4, 4, 48, 48, 48, 48, 48, 48, 4, 4, 4, 844, 960, 963, 832, 1012, 1015, 4, 4, 4, 895, 1012, 1015, 883, 960, 963, 4, 4, 4, 48, 48, 48, 48, 48, 48, 4, 4, 4, 895, 963, 960, 883, 1015, 1012, 4, 4, 4, 844, 1015, 1012, 832, 963, 960, 3, 4, 4, 3, 8, 8, 3, 8, 8, 3, 4, 4, 3, 8, 8, 3, 8, 8, 3, 4, 4, 3, 8, 8, 3]

theorem obstructionChunk115 (code : Fin 19683)
    (_hlo : 14720 ≤ code.val) (hhi : code.val < 14848) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (14720 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 14720, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 14720 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
