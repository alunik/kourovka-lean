import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[3, 1856, 1867, 1066, 988, 991, 1066, 1164, 905, 1066, 902, 1809, 1111, 1066, 1981, 1164, 244, 247, 632, 117, 251, 1095, 1796, 1066, 620, 196, 118, 2048, 200, 203, 1081, 991, 988, 1081, 902, 1164, 1081, 1842, 905, 1104, 1980, 1081, 1164, 246, 245, 634, 250, 122, 1088, 1081, 1831, 622, 121, 197, 2063, 202, 201, 3, 905, 902, 3, 877, 862, 3, 865, 850, 3, 905, 902, 3, 828, 829, 3, 1984, 2035, 3, 905, 902, 3, 2048, 2063, 3, 768, 769, 1058, 960, 963, 1058, 905, 2176, 1058, 1392, 902, 1114, 1058, 2063, 596, 73, 255, 2176, 240, 243, 1098, 1356, 1058, 2240, 204, 207, 576, 192, 74, 1073, 963, 960, 1073, 2195, 902, 1073, 905, 1393, 1117, 2048, 1073, 598, 254, 70, 2195, 242]

theorem obstructionChunk147 (code : Fin 19683)
    (_hlo : 18816 ≤ code.val) (hhi : code.val < 18944) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (18816 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 18816, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 18816 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
