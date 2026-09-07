import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[895, 844, 3, 883, 832, 3, 4, 4, 3, 1104, 1111, 3, 1111, 1104, 3, 4, 4, 3, 1088, 1095, 3, 1095, 1088, 4, 4, 4, 598, 598, 598, 578, 578, 578, 4, 4, 4, 766, 2164, 844, 763, 2048, 832, 4, 4, 4, 718, 895, 2233, 715, 883, 1350, 4, 4, 4, 596, 596, 596, 576, 576, 576, 4, 4, 4, 757, 895, 2164, 752, 883, 2063, 4, 4, 4, 709, 2218, 844, 704, 1351, 832, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 12, 12, 1, 48, 48, 1, 48, 48, 1, 12, 12, 1, 1104, 1117, 1, 1117, 1104, 1, 12, 12, 1, 1088, 1101]

theorem obstructionChunk119 (code : Fin 19683)
    (_hlo : 15232 ≤ code.val) (hhi : code.val < 15360) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (15232 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 15232, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 15232 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
