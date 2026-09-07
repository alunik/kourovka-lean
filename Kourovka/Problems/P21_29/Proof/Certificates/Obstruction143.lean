import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[578, 578, 3, 48, 48, 3, 48, 48, 3, 48, 48, 3, 768, 769, 3, 679, 644, 3, 675, 640, 3, 828, 829, 3, 661, 694, 3, 657, 690, 48, 48, 48, 48, 48, 48, 48, 48, 48, 1111, 768, 769, 865, 1164, 1111, 877, 1111, 1981, 1095, 828, 829, 850, 1164, 1095, 862, 1095, 1827, 48, 48, 48, 48, 48, 48, 48, 48, 48, 1104, 768, 769, 850, 1104, 1164, 862, 1980, 1104, 1088, 828, 829, 865, 1088, 1164, 877, 1792, 1088, 3, 48, 48, 3, 48, 48, 3, 48, 48, 3, 828, 829, 3, 679, 644, 3, 675, 640, 3, 768, 769, 3, 661, 694, 3, 657, 690, 48, 48, 48, 48, 48, 48, 48, 48, 48, 1114, 828, 829, 877, 1114, 2167, 865, 2080, 1114]

theorem obstructionChunk143 (code : Fin 19683)
    (_hlo : 18304 ≤ code.val) (hhi : code.val < 18432) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (18304 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 18304, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 18304 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
