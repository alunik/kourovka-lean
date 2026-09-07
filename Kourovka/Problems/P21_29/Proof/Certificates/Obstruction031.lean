import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[960, 3, 16, 16, 3, 16, 16, 3, 16, 16, 3, 1058, 1073, 3, 1058, 1073, 3, 1058, 1073, 3, 1073, 1058, 3, 1073, 1058, 3, 1073, 1058, 16, 16, 16, 16, 16, 16, 16, 16, 16, 578, 578, 578, 657, 1156, 709, 661, 704, 1160, 598, 598, 598, 640, 1156, 757, 644, 752, 1160, 16, 16, 16, 16, 16, 16, 16, 16, 16, 576, 576, 576, 690, 718, 1156, 694, 1160, 715, 596, 596, 596, 675, 766, 1156, 679, 1160, 763, 3, 16, 16, 3, 16, 16, 3, 16, 16, 3, 1066, 1081, 3, 1066, 1081, 3, 1066, 1081, 3, 1081, 1066, 3, 1081, 1066, 3, 1081, 1066, 16, 16, 16, 16, 16, 16, 16, 16, 16, 622, 622, 622, 657, 718, 1156, 661, 1200, 715, 634]

theorem obstructionChunk031 (code : Fin 19683)
    (_hlo : 3968 ≤ code.val) (hhi : code.val < 4096) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (3968 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 3968, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 3968 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
