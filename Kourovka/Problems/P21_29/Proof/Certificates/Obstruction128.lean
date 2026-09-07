import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[792, 793, 3, 1160, 1160, 1043, 988, 991, 1043, 928, 1156, 1043, 1160, 943, 1104, 1160, 1043, 1156, 208, 211, 576, 220, 80, 1088, 1043, 1160, 596, 83, 227, 1160, 236, 239, 1024, 991, 988, 1024, 1156, 943, 1024, 928, 1160, 1111, 1024, 1160, 1156, 210, 209, 578, 95, 221, 1095, 1160, 1024, 598, 226, 92, 1160, 238, 237, 3, 943, 928, 3, 862, 877, 3, 850, 865, 3, 943, 928, 3, 792, 793, 3, 1200, 1200, 3, 943, 928, 3, 1156, 1156, 3, 804, 805, 1051, 960, 963, 1051, 1156, 928, 1051, 943, 2167, 1117, 1200, 1051, 620, 216, 108, 1200, 212, 215, 1101, 1051, 2167, 1156, 232, 235, 632, 111, 231, 1032, 963, 960, 1032, 943, 1156, 1032, 2167, 928, 1114, 1032, 1200, 622, 99, 217]

theorem obstructionChunk128 (code : Fin 19683)
    (_hlo : 16384 ≤ code.val) (hhi : code.val < 16512) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (16384 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 16384, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 16384 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
