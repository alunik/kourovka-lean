import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[12, 12, 3, 763, 752, 3, 757, 766, 3, 12, 12, 3, 715, 704, 3, 709, 718, 12, 12, 12, 937, 804, 805, 934, 792, 793, 12, 12, 12, 937, 1168, 679, 934, 1168, 675, 12, 12, 12, 937, 694, 1772, 934, 690, 1867, 12, 12, 12, 934, 804, 805, 937, 792, 793, 12, 12, 12, 934, 644, 1168, 937, 640, 1168, 12, 12, 12, 934, 1774, 661, 937, 1856, 657, 3, 934, 937, 3, 883, 832, 3, 895, 844, 3, 934, 937, 3, 804, 805, 3, 1168, 1168, 3, 934, 937, 3, 1164, 1164, 3, 792, 793, 1081, 960, 963, 1081, 1164, 937, 1081, 934, 2143, 1095, 1168, 1081, 632, 228, 101, 1168, 232, 235, 1111, 1081, 2143, 1164, 212, 215, 620, 102, 219, 1066, 963, 960]

theorem obstructionChunk095 (code : Fin 19683)
    (_hlo : 12160 ≤ code.val) (hhi : code.val < 12288) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (12160 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 12160, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 12160 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
