import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[3, 1024, 1043, 3, 1024, 1043, 3, 1043, 1024, 3, 1043, 1024, 3, 1043, 1024, 16, 16, 16, 16, 16, 16, 16, 16, 16, 622, 622, 622, 690, 1156, 757, 694, 752, 1160, 634, 634, 634, 675, 1156, 709, 679, 704, 1160, 16, 16, 16, 16, 16, 16, 16, 16, 16, 620, 620, 620, 657, 766, 1156, 661, 1160, 763, 632, 632, 632, 640, 718, 1156, 644, 1160, 715, 3, 16, 16, 3, 16, 16, 3, 16, 16, 3, 1032, 1051, 3, 1032, 1051, 3, 1032, 1051, 3, 1051, 1032, 3, 1051, 1032, 3, 1051, 1032, 16, 16, 16, 16, 16, 16, 16, 16, 16, 578, 578, 578, 690, 766, 1156, 694, 1750, 763, 598, 598, 598, 675, 718, 1156, 679, 1984, 715, 16, 16, 16, 16, 16]

theorem obstructionChunk033 (code : Fin 19683)
    (_hlo : 4224 ≤ code.val) (hhi : code.val < 4352) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (4224 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 4224, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 4224 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
