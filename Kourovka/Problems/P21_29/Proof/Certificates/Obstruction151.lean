import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[230, 578, 233, 66, 1081, 1003, 1000, 1081, 1164, 943, 1081, 928, 1784, 1117, 1200, 1081, 596, 215, 78, 1200, 219, 216, 1101, 1081, 1772, 1164, 231, 228, 576, 77, 232, 3, 943, 928, 3, 844, 895, 3, 832, 883, 3, 943, 928, 3, 1200, 1200, 3, 829, 828, 3, 943, 928, 3, 769, 768, 3, 1842, 1809, 1058, 1012, 1015, 1058, 1981, 928, 1058, 943, 2269, 1111, 1058, 1200, 1200, 221, 222, 634, 125, 210, 1095, 2253, 1058, 622, 237, 126, 2017, 225, 226, 1073, 1015, 1012, 1073, 943, 1980, 1073, 2266, 928, 1104, 1200, 1073, 1200, 223, 220, 632, 211, 114, 1088, 1073, 2250, 620, 113, 236, 2002, 227, 224, 3, 12, 12, 3, 829, 828, 3, 769, 768, 3, 12, 12, 3, 757, 766, 3]

theorem obstructionChunk151 (code : Fin 19683)
    (_hlo : 19328 ≤ code.val) (hhi : code.val < 19456) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (19328 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 19328, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 19328 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
