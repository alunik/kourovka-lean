import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[4, 3, 1088, 1095, 3, 1095, 1088, 3, 4, 4, 3, 1104, 1111, 3, 1111, 1104, 4, 4, 4, 48, 48, 48, 48, 48, 48, 4, 4, 4, 877, 1000, 1003, 865, 988, 991, 4, 4, 4, 862, 988, 991, 850, 1000, 1003, 4, 4, 4, 48, 48, 48, 48, 48, 48, 4, 4, 4, 862, 1003, 1000, 850, 991, 988, 4, 4, 4, 877, 991, 988, 865, 1003, 1000, 3, 4, 4, 3, 8, 8, 3, 8, 8, 3, 4, 4, 3, 8, 8, 3, 8, 8, 3, 4, 4, 3, 8, 8, 3, 8, 8, 4, 4, 4, 8, 8, 8, 8, 8, 8, 4, 4, 4, 8, 8, 8, 8, 8, 8, 4, 4, 4, 8, 8, 8, 8, 8, 8, 4, 4, 4, 8]

theorem obstructionChunk064 (code : Fin 19683)
    (_hlo : 8192 ≤ code.val) (hhi : code.val < 8320) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (8192 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 8192, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 8192 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
