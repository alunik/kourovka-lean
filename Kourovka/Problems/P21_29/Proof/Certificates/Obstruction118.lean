import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[4, 8, 8, 8, 8, 8, 8, 4, 4, 4, 8, 8, 8, 8, 8, 8, 4, 4, 4, 8, 8, 8, 8, 8, 8, 4, 4, 4, 8, 8, 8, 8, 8, 8, 4, 4, 4, 8, 8, 8, 8, 8, 8, 3, 4, 4, 3, 883, 832, 3, 895, 844, 3, 4, 4, 3, 1114, 1117, 3, 1117, 1114, 3, 4, 4, 3, 1098, 1101, 3, 1101, 1098, 4, 4, 4, 622, 622, 622, 634, 634, 634, 4, 4, 4, 757, 1164, 832, 752, 1945, 844, 4, 4, 4, 709, 883, 1164, 704, 895, 1813, 4, 4, 4, 620, 620, 620, 632, 632, 632, 4, 4, 4, 766, 883, 1164, 763, 895, 1944, 4, 4, 4, 718, 1164, 832, 715, 1846, 844, 3, 4, 4, 3]

theorem obstructionChunk118 (code : Fin 19683)
    (_hlo : 15104 ≤ code.val) (hhi : code.val < 15232) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (15104 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 15104, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 15104 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
