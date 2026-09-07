import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[4, 4, 704, 1164, 850, 709, 1796, 862, 4, 4, 4, 622, 622, 622, 634, 634, 634, 4, 4, 4, 763, 1164, 850, 766, 1944, 862, 4, 4, 4, 715, 865, 1164, 718, 877, 1831, 3, 4, 4, 3, 877, 862, 3, 865, 850, 3, 4, 4, 3, 1114, 1117, 3, 1117, 1114, 3, 4, 4, 3, 1098, 1101, 3, 1101, 1098, 4, 4, 4, 596, 596, 596, 576, 576, 576, 4, 4, 4, 763, 877, 2167, 766, 865, 2057, 4, 4, 4, 715, 2184, 862, 718, 1348, 850, 4, 4, 4, 598, 598, 598, 578, 578, 578, 4, 4, 4, 752, 2167, 862, 757, 2054, 850, 4, 4, 4, 704, 877, 2203, 709, 865, 1349, 3, 4, 4, 3, 8, 8, 3, 8, 8, 3, 4, 4]

theorem obstructionChunk113 (code : Fin 19683)
    (_hlo : 14464 ≤ code.val) (hhi : code.val < 14592) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (14464 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 14464, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 14464 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
