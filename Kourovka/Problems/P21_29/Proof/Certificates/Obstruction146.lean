import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[1980, 934, 1024, 937, 2263, 1117, 1024, 1200, 1200, 222, 221, 634, 119, 209, 1101, 2247, 1024, 622, 238, 116, 2035, 226, 225, 3, 12, 12, 3, 828, 829, 3, 768, 769, 3, 12, 12, 3, 763, 752, 3, 757, 766, 3, 12, 12, 3, 715, 704, 3, 709, 718, 12, 12, 12, 905, 828, 829, 902, 768, 769, 12, 12, 12, 905, 679, 2143, 902, 675, 2048, 12, 12, 12, 905, 2184, 694, 902, 1352, 690, 12, 12, 12, 902, 828, 829, 905, 768, 769, 12, 12, 12, 902, 2143, 644, 905, 2063, 640, 12, 12, 12, 902, 661, 2203, 905, 657, 1353, 3, 902, 905, 3, 865, 850, 3, 877, 862, 3, 902, 905, 3, 1164, 1164, 3, 768, 769, 3, 902, 905, 3, 828, 829]

theorem obstructionChunk146 (code : Fin 19683)
    (_hlo : 18688 ≤ code.val) (hhi : code.val < 18816) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (18688 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 18688, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 18688 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
