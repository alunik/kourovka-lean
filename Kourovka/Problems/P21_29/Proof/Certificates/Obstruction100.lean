import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[896, 3, 862, 877, 3, 850, 865, 3, 911, 896, 3, 793, 792, 3, 1168, 1168, 3, 911, 896, 3, 1184, 1184, 3, 805, 804, 1073, 1000, 1003, 1073, 1184, 896, 1073, 911, 1184, 1095, 1168, 1073, 634, 205, 109, 1168, 193, 194, 1111, 1073, 1184, 1184, 253, 254, 622, 110, 242, 1058, 1003, 1000, 1058, 911, 1184, 1058, 1184, 896, 1088, 1058, 1168, 632, 98, 204, 1168, 195, 192, 1104, 1184, 1058, 1184, 255, 252, 620, 243, 97, 3, 12, 12, 3, 805, 804, 3, 793, 792, 3, 12, 12, 3, 757, 766, 3, 763, 752, 3, 12, 12, 3, 709, 718, 3, 715, 704, 12, 12, 12, 928, 805, 804, 943, 793, 792, 12, 12, 12, 928, 694, 1168, 943, 690, 1168, 12, 12, 12, 928]

theorem obstructionChunk100 (code : Fin 19683)
    (_hlo : 12800 ≤ code.val) (hhi : code.val < 12928) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (12800 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 12800, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 12800 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
