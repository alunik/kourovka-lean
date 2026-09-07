import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[1066, 934, 1164, 1066, 2143, 937, 1088, 1066, 1168, 634, 106, 229, 1168, 234, 233, 1104, 2143, 1066, 1164, 214, 213, 622, 218, 105, 3, 937, 934, 3, 895, 844, 3, 883, 832, 3, 937, 934, 3, 1168, 1168, 3, 792, 793, 3, 937, 934, 3, 804, 805, 3, 2176, 2195, 1073, 988, 991, 1073, 937, 1748, 1073, 1904, 934, 1098, 1168, 1073, 1168, 236, 239, 596, 224, 89, 1114, 1073, 1861, 576, 90, 223, 1792, 208, 211, 1058, 991, 988, 1058, 1750, 934, 1058, 937, 1915, 1101, 1058, 1168, 1168, 238, 237, 598, 86, 225, 1117, 1870, 1058, 578, 222, 85, 1827, 210, 209, 3, 12, 12, 3, 48, 48, 3, 48, 48, 3, 12, 12, 3, 694, 661, 3, 690, 657, 3, 12, 12, 3, 644]

theorem obstructionChunk096 (code : Fin 19683)
    (_hlo : 12288 ≤ code.val) (hhi : code.val < 12416) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (12288 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 12288, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 12288 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
