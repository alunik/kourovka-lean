import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[225, 622, 126, 237, 1111, 1160, 1058, 634, 210, 125, 1160, 222, 221, 3, 943, 928, 3, 895, 844, 3, 883, 832, 3, 943, 928, 3, 828, 829, 3, 1168, 1168, 3, 943, 928, 3, 1156, 1156, 3, 768, 769, 1081, 1000, 1003, 1081, 1156, 928, 1081, 943, 1945, 1101, 1168, 1081, 576, 232, 77, 1168, 228, 231, 1117, 1081, 1957, 1156, 216, 219, 596, 78, 215, 1066, 1003, 1000, 1066, 943, 1156, 1066, 1944, 928, 1098, 1066, 1168, 578, 66, 233, 1168, 230, 229, 1114, 1956, 1066, 1156, 218, 217, 598, 214, 65, 3, 12, 12, 3, 48, 48, 3, 48, 48, 3, 12, 12, 3, 690, 657, 3, 694, 661, 3, 12, 12, 3, 640, 675, 3, 644, 679, 12, 12, 12, 48, 48, 48, 48]

theorem obstructionChunk079 (code : Fin 19683)
    (_hlo : 10112 ≤ code.val) (hhi : code.val < 10240) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (10112 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 10112, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 10112 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
