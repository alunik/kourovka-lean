import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[1, 1024, 1073, 1, 1024, 1073, 1, 1073, 1024, 1, 1073, 1024, 1, 1073, 1024, 1, 48, 48, 1, 48, 48, 1, 48, 48, 1, 1058, 1043, 1, 1058, 1043, 1, 1058, 1043, 1, 1043, 1058, 1, 1043, 1058, 1, 1043, 1058, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 12, 12, 1, 644, 661, 1, 640, 657, 1, 12, 12, 1, 1098, 1095, 1, 1095, 1098, 1, 12, 12, 1, 1114, 1111, 1, 1111, 1114, 1, 12, 12, 1, 694, 679, 1, 690, 675, 1, 12, 12, 1, 1088, 1101, 1, 1101, 1088, 1, 12, 12, 1, 1104, 1117, 1, 1117, 1104, 1, 2, 2, 1, 2]

theorem obstructionChunk087 (code : Fin 19683)
    (_hlo : 11136 ≤ code.val) (hhi : code.val < 11264) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (11136 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 11136, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 11136 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
