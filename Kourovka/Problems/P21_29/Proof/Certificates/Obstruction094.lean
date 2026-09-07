import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[203, 1111, 1184, 1032, 576, 244, 87, 1184, 248, 251, 1051, 1015, 1012, 1051, 902, 1164, 1051, 1184, 905, 1088, 1168, 1051, 1164, 198, 197, 598, 202, 91, 1104, 1051, 1184, 578, 88, 245, 1184, 250, 249, 3, 905, 902, 3, 844, 895, 3, 832, 883, 3, 905, 902, 3, 792, 793, 3, 1168, 1168, 3, 905, 902, 3, 1184, 1184, 3, 804, 805, 1024, 1000, 1003, 1024, 905, 1184, 1024, 1184, 902, 1098, 1024, 1168, 632, 104, 207, 1168, 192, 195, 1114, 1184, 1024, 1184, 252, 255, 620, 240, 107, 1043, 1003, 1000, 1043, 1184, 902, 1043, 905, 1184, 1101, 1168, 1043, 634, 206, 103, 1168, 194, 193, 1117, 1043, 1184, 1184, 254, 253, 622, 100, 241, 3, 12, 12, 3, 804, 805, 3, 792, 793, 3]

theorem obstructionChunk094 (code : Fin 19683)
    (_hlo : 12032 ≤ code.val) (hhi : code.val < 12160) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (12032 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 12032, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 12032 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
