import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[12, 12, 1, 1114, 1111, 1, 1111, 1114, 1, 12, 12, 1, 1098, 1095, 1, 1095, 1098, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 988, 991, 1, 657, 640, 1, 661, 644, 1, 704, 709, 1, 1156, 1156, 1, 988, 991, 1, 752, 757, 1, 988, 991, 1, 1160, 1160, 1, 991, 988, 1, 675, 690, 1, 679, 694, 1, 718, 715, 1, 1156, 1156, 1, 991, 988, 1, 766, 763, 1, 991, 988, 1, 1160, 1160, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 960, 963]

theorem obstructionChunk122 (code : Fin 19683)
    (_hlo : 15616 ≤ code.val) (hhi : code.val < 15744) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (15616 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 15616, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 15616 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
