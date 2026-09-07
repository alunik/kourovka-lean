import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[690, 1015, 1012, 12, 12, 12, 679, 1015, 1012, 675, 1003, 1000, 3, 16, 16, 3, 16, 16, 3, 16, 16, 3, 1066, 1081, 3, 1066, 1081, 3, 1066, 1081, 3, 1081, 1066, 3, 1081, 1066, 3, 1081, 1066, 16, 16, 16, 16, 16, 16, 16, 16, 16, 598, 598, 598, 661, 709, 1164, 657, 1200, 704, 578, 578, 578, 644, 757, 1164, 640, 1774, 752, 16, 16, 16, 16, 16, 16, 16, 16, 16, 596, 596, 596, 694, 1164, 718, 690, 715, 1200, 576, 576, 576, 679, 1164, 766, 675, 763, 1772, 3, 16, 16, 3, 16, 16, 3, 16, 16, 3, 1058, 1073, 3, 1058, 1073, 3, 1058, 1073, 3, 1073, 1058, 3, 1073, 1058, 3, 1073, 1058, 16, 16, 16, 16, 16, 16, 16, 16]

theorem obstructionChunk048 (code : Fin 19683)
    (_hlo : 6144 ≤ code.val) (hhi : code.val < 6272) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (6144 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 6144, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 6144 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
