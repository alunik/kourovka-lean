import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[709, 3, 704, 715, 3, 12, 12, 3, 766, 757, 3, 752, 763, 12, 12, 12, 937, 793, 792, 934, 805, 804, 12, 12, 12, 937, 657, 1156, 934, 661, 1200, 12, 12, 12, 937, 1156, 640, 934, 2152, 644, 12, 12, 12, 934, 793, 792, 937, 805, 804, 12, 12, 12, 934, 1156, 690, 937, 1200, 694, 12, 12, 12, 934, 675, 1156, 937, 679, 2152, 3, 934, 937, 3, 832, 883, 3, 844, 895, 3, 934, 937, 3, 1156, 1156, 3, 805, 804, 3, 934, 937, 3, 793, 792, 3, 1160, 1160, 1058, 988, 991, 1058, 1156, 937, 1058, 934, 1160, 1117, 1058, 1160, 1156, 209, 210, 578, 85, 222, 1101, 1160, 1058, 598, 225, 86, 1160, 237, 238, 1073, 991, 988, 1073, 934, 1156, 1073]

theorem obstructionChunk133 (code : Fin 19683)
    (_hlo : 17024 ≤ code.val) (hhi : code.val < 17152) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (17024 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 17024, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 17024 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
