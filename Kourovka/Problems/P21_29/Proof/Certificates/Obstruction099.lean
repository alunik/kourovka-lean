import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[12, 12, 12, 896, 1168, 661, 911, 1168, 657, 12, 12, 12, 896, 644, 1184, 911, 640, 1184, 12, 12, 12, 911, 793, 792, 896, 805, 804, 12, 12, 12, 911, 694, 1168, 896, 690, 1168, 12, 12, 12, 911, 1184, 679, 896, 1184, 675, 3, 896, 911, 3, 850, 865, 3, 862, 877, 3, 896, 911, 3, 1164, 1164, 3, 805, 804, 3, 896, 911, 3, 793, 792, 3, 1184, 1184, 1081, 1012, 1015, 1081, 896, 1164, 1081, 1184, 911, 1098, 1168, 1081, 1164, 197, 198, 598, 201, 81, 1114, 1081, 1184, 578, 82, 246, 1184, 249, 250, 1066, 1015, 1012, 1066, 1164, 911, 1066, 896, 1184, 1101, 1066, 1168, 1164, 199, 196, 596, 94, 200, 1117, 1184, 1066, 576, 247, 93, 1184, 251, 248, 3, 911]

theorem obstructionChunk099 (code : Fin 19683)
    (_hlo : 12672 ≤ code.val) (hhi : code.val < 12800) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (12672 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 12672, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 12672 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
