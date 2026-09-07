import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[48, 48, 48, 48, 48, 1095, 804, 805, 832, 1164, 1095, 844, 1095, 1168, 1111, 792, 793, 883, 1164, 1111, 895, 1111, 2155, 48, 48, 48, 48, 48, 48, 48, 48, 48, 1088, 804, 805, 883, 1088, 1164, 895, 1168, 1088, 1104, 792, 793, 832, 1104, 1164, 844, 2155, 1104, 3, 48, 48, 3, 48, 48, 3, 48, 48, 3, 792, 793, 3, 644, 679, 3, 640, 675, 3, 804, 805, 3, 694, 661, 3, 690, 657, 48, 48, 48, 48, 48, 48, 48, 48, 48, 1098, 792, 793, 844, 1098, 1168, 832, 1168, 1098, 1114, 804, 805, 895, 1114, 1772, 883, 1904, 1114, 48, 48, 48, 48, 48, 48, 48, 48, 48, 1101, 792, 793, 895, 1168, 1101, 883, 1101, 1168, 1117, 804, 805, 844, 1774, 1117]

theorem obstructionChunk092 (code : Fin 19683)
    (_hlo : 11776 ≤ code.val) (hhi : code.val < 11904) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (11776 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 11776, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 11776 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
