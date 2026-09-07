import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[1774, 679, 943, 1870, 675, 12, 12, 12, 943, 805, 804, 928, 793, 792, 12, 12, 12, 943, 1168, 661, 928, 1168, 657, 12, 12, 12, 943, 644, 1772, 928, 640, 1861, 3, 928, 943, 3, 865, 850, 3, 877, 862, 3, 928, 943, 3, 805, 804, 3, 1168, 1168, 3, 928, 943, 3, 1164, 1164, 3, 793, 792, 1032, 960, 963, 1032, 928, 1164, 1032, 2140, 943, 1098, 1032, 1168, 634, 96, 230, 1168, 233, 234, 1114, 2140, 1032, 1164, 213, 214, 622, 217, 99, 1051, 963, 960, 1051, 1164, 943, 1051, 928, 2140, 1101, 1168, 1051, 632, 231, 111, 1168, 235, 232, 1117, 1051, 2140, 1164, 215, 212, 620, 108, 216, 3, 943, 928, 3, 877, 862, 3, 865, 850, 3, 943, 928, 3, 1168, 1168]

theorem obstructionChunk101 (code : Fin 19683)
    (_hlo : 12928 ≤ code.val) (hhi : code.val < 13056) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (12928 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 12928, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 12928 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
