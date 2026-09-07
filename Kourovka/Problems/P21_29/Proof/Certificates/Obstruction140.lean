import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[2, 2, 1, 2, 2, 1, 2, 2, 1, 1012, 1015, 1, 661, 644, 1, 657, 640, 1, 715, 718, 1, 1200, 1200, 1, 1012, 1015, 1, 763, 766, 1, 1012, 1015, 1, 2176, 2225, 1, 1015, 1012, 1, 679, 694, 1, 675, 690, 1, 709, 704, 1, 1200, 1200, 1, 1015, 1012, 1, 757, 752, 1, 1015, 1012, 1, 2210, 2195, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 12, 12, 1, 679, 694, 1, 675, 690, 1, 12, 12, 1, 1114, 1111, 1, 1111, 1114, 1, 12, 12, 1, 1098, 1095, 1, 1095, 1098, 1, 12, 12, 1, 661, 644, 1, 657, 640, 1, 12, 12]

theorem obstructionChunk140 (code : Fin 19683)
    (_hlo : 17920 ≤ code.val) (hhi : code.val < 18048) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (17920 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 17920, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 17920 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
