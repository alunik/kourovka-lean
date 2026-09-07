import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[4, 3, 1088, 1095, 3, 1095, 1088, 4, 4, 4, 48, 48, 48, 48, 48, 48, 4, 4, 4, 865, 1000, 1003, 877, 988, 991, 4, 4, 4, 850, 988, 991, 862, 1000, 1003, 4, 4, 4, 48, 48, 48, 48, 48, 48, 4, 4, 4, 850, 1003, 1000, 862, 991, 988, 4, 4, 4, 865, 991, 988, 877, 1003, 1000, 3, 4, 4, 3, 48, 48, 3, 48, 48, 3, 4, 4, 3, 1114, 1117, 3, 1117, 1114, 3, 4, 4, 3, 1098, 1101, 3, 1101, 1098, 4, 4, 4, 48, 48, 48, 48, 48, 48, 4, 4, 4, 877, 960, 963, 865, 1012, 1015, 4, 4, 4, 862, 1012, 1015, 850, 960, 963, 4, 4, 4, 48, 48, 48, 48, 48, 48, 4, 4, 4, 862]

theorem obstructionChunk109 (code : Fin 19683)
    (_hlo : 13952 ≤ code.val) (hhi : code.val < 14080) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (13952 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 13952, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 13952 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
