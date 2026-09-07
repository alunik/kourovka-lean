import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[1098, 768, 769, 862, 1098, 2225, 850, 1376, 1098, 48, 48, 48, 48, 48, 48, 48, 48, 48, 1117, 828, 829, 862, 2167, 1117, 850, 1117, 2095, 1101, 768, 769, 877, 2210, 1101, 865, 1101, 1377, 3, 12, 12, 3, 768, 769, 3, 828, 829, 3, 12, 12, 3, 715, 704, 3, 709, 718, 3, 12, 12, 3, 763, 752, 3, 757, 766, 12, 12, 12, 937, 768, 769, 934, 828, 829, 12, 12, 12, 937, 1200, 644, 934, 1200, 640, 12, 12, 12, 937, 661, 1981, 934, 657, 2253, 12, 12, 12, 934, 768, 769, 937, 828, 829, 12, 12, 12, 934, 679, 1200, 937, 675, 1200, 12, 12, 12, 934, 1980, 694, 937, 2250, 690, 3, 934, 937, 3, 850, 865, 3, 862, 877, 3, 934]

theorem obstructionChunk144 (code : Fin 19683)
    (_hlo : 18432 ≤ code.val) (hhi : code.val < 18560) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (18432 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 18432, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 18432 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
