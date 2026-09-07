import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[769, 768, 832, 1114, 1164, 844, 1981, 1114, 1098, 829, 828, 883, 1098, 1164, 895, 1842, 1098, 48, 48, 48, 48, 48, 48, 48, 48, 48, 1117, 769, 768, 883, 1164, 1117, 895, 1117, 1980, 1101, 829, 828, 832, 1164, 1101, 844, 1101, 1809, 3, 48, 48, 3, 48, 48, 3, 48, 48, 3, 829, 828, 3, 661, 694, 3, 657, 690, 3, 769, 768, 3, 679, 644, 3, 675, 640, 48, 48, 48, 48, 48, 48, 48, 48, 48, 1111, 829, 828, 844, 2164, 1111, 832, 1111, 2089, 1095, 769, 768, 895, 2176, 1095, 883, 1095, 1378, 48, 48, 48, 48, 48, 48, 48, 48, 48, 1104, 829, 828, 895, 1104, 2164, 883, 2086, 1104, 1088, 769, 768, 844, 1088, 2195, 832, 1379, 1088, 3, 12, 12]

theorem obstructionChunk149 (code : Fin 19683)
    (_hlo : 19072 ≤ code.val) (hhi : code.val < 19200) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (19072 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 19072, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 19072 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
