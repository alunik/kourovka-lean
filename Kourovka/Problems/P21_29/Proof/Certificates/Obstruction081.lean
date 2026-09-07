import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[3, 48, 48, 3, 48, 48, 3, 48, 48, 3, 829, 828, 3, 690, 657, 3, 694, 661, 3, 769, 768, 3, 640, 675, 3, 644, 679, 48, 48, 48, 48, 48, 48, 48, 48, 48, 1088, 829, 828, 877, 1088, 1156, 865, 1168, 1088, 1104, 769, 768, 862, 1104, 1156, 850, 1957, 1104, 48, 48, 48, 48, 48, 48, 48, 48, 48, 1095, 829, 828, 862, 1156, 1095, 850, 1095, 1168, 1111, 769, 768, 877, 1156, 1111, 865, 1111, 1956, 3, 12, 12, 3, 769, 768, 3, 829, 828, 3, 12, 12, 3, 718, 709, 3, 704, 715, 3, 12, 12, 3, 766, 757, 3, 752, 763, 12, 12, 12, 905, 769, 768, 902, 829, 828, 12, 12, 12, 905, 1156, 657, 902, 1168, 661, 12, 12]

theorem obstructionChunk081 (code : Fin 19683)
    (_hlo : 10368 ≤ code.val) (hhi : code.val < 10496) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (10368 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 10368, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 10368 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
