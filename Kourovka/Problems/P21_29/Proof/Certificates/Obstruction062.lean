import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[2155, 844, 3, 4, 4, 3, 895, 844, 3, 883, 832, 3, 4, 4, 3, 1098, 1101, 3, 1101, 1098, 3, 4, 4, 3, 1114, 1117, 3, 1117, 1114, 4, 4, 4, 576, 576, 576, 596, 596, 596, 4, 4, 4, 763, 1168, 844, 766, 1168, 832, 4, 4, 4, 715, 895, 1748, 718, 883, 1856, 4, 4, 4, 578, 578, 578, 598, 598, 598, 4, 4, 4, 752, 895, 1168, 757, 883, 1168, 4, 4, 4, 704, 1750, 844, 709, 1867, 832, 3, 4, 4, 3, 8, 8, 3, 8, 8, 3, 4, 4, 3, 8, 8, 3, 8, 8, 3, 4, 4, 3, 8, 8, 3, 8, 8, 4, 4, 4, 8, 8, 8, 8, 8, 8, 4, 4, 4, 8, 8, 8, 8, 8, 8]

theorem obstructionChunk062 (code : Fin 19683)
    (_hlo : 7936 ≤ code.val) (hhi : code.val < 8064) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (7936 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 7936, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 7936 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
