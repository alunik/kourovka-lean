import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[937, 3, 768, 769, 3, 1200, 1200, 3, 934, 937, 3, 1164, 1164, 3, 828, 829, 1051, 1000, 1003, 1051, 1164, 937, 1051, 934, 1784, 1111, 1200, 1051, 596, 212, 68, 1200, 216, 219, 1095, 1051, 1772, 1164, 228, 231, 576, 71, 235, 1032, 1003, 1000, 1032, 934, 1164, 1032, 1786, 937, 1104, 1032, 1200, 598, 75, 213, 1200, 218, 217, 1088, 1774, 1032, 1164, 230, 229, 578, 234, 72, 3, 937, 934, 3, 862, 877, 3, 850, 865, 3, 937, 934, 3, 1200, 1200, 3, 828, 829, 3, 937, 934, 3, 768, 769, 3, 1792, 1827, 1043, 1012, 1015, 1043, 937, 1981, 1043, 2256, 934, 1114, 1200, 1043, 1200, 220, 223, 632, 208, 120, 1098, 1043, 2240, 620, 123, 239, 1984, 224, 227, 1024, 1015, 1012, 1024]

theorem obstructionChunk145 (code : Fin 19683)
    (_hlo : 18560 ≤ code.val) (hhi : code.val < 18688) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (18560 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 18560, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 18560 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
