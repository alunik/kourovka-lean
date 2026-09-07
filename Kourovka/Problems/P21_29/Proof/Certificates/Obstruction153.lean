import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[1117, 1032, 1980, 1164, 247, 244, 632, 127, 248, 1101, 1846, 1032, 620, 199, 124, 2054, 203, 200, 3, 911, 896, 3, 895, 844, 3, 883, 832, 3, 911, 896, 3, 829, 828, 3, 2002, 2017, 3, 911, 896, 3, 2054, 2057, 3, 769, 768, 1043, 960, 963, 1043, 2225, 896, 1043, 911, 1394, 1111, 2054, 1043, 598, 253, 76, 2225, 241, 242, 1095, 1043, 1358, 2253, 205, 206, 578, 79, 194, 1024, 963, 960, 1024, 911, 2210, 1024, 1395, 896, 1104, 1024, 2057, 596, 67, 252, 2210, 243, 240, 1088, 1359, 1024, 2250, 207, 204, 576, 195, 64]

theorem obstructionChunk153 (code : Fin 19683)
    (_hlo : 19584 ≤ code.val) (_hhi : code.val < 19683) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 99,
      obstructionCheck (19584 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 99 := ⟨code.val - 19584, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 19584 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
