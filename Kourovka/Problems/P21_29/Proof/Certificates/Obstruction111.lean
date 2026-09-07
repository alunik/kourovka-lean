import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[576, 576, 576, 4, 4, 4, 704, 1164, 865, 709, 1200, 877, 4, 4, 4, 752, 850, 1164, 757, 862, 1784, 4, 4, 4, 598, 598, 598, 578, 578, 578, 4, 4, 4, 715, 850, 1164, 718, 862, 1200, 4, 4, 4, 763, 1164, 865, 766, 1786, 877, 3, 4, 4, 3, 862, 877, 3, 850, 865, 3, 4, 4, 3, 1114, 1117, 3, 1117, 1114, 3, 4, 4, 3, 1098, 1101, 3, 1101, 1098, 4, 4, 4, 620, 620, 620, 632, 632, 632, 4, 4, 4, 715, 1200, 877, 718, 1200, 865, 4, 4, 4, 763, 862, 1957, 766, 850, 2247, 4, 4, 4, 622, 622, 622, 634, 634, 634, 4, 4, 4, 704, 862, 1200, 709, 850, 1200, 4, 4, 4, 752, 1956, 877, 757, 2240]

theorem obstructionChunk111 (code : Fin 19683)
    (_hlo : 14208 ≤ code.val) (hhi : code.val < 14336) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (14208 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 14208, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 14208 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
