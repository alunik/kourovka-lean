import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 960, 963, 1, 640, 657, 1, 644, 661, 1, 704, 709, 1, 960, 963, 1, 1160, 1160, 1, 752, 757, 1, 1156, 1156, 1, 960, 963, 1, 963, 960, 1, 690, 675, 1, 694, 679, 1, 718, 715, 1, 963, 960, 1, 1160, 1160, 1, 766, 763, 1, 1156, 1156, 1, 963, 960, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 988, 991, 1, 640, 657, 1, 644, 661, 1, 718, 715, 1, 1156, 1156, 1, 988, 991, 1, 766, 763, 1, 988, 991, 1, 1184, 1184, 1, 991, 988, 1, 690, 675, 1, 694, 679]

theorem obstructionChunk071 (code : Fin 19683)
    (_hlo : 9088 ≤ code.val) (hhi : code.val < 9216) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (9088 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 9088, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 9088 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
