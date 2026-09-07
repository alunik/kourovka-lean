import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[4, 4, 4, 8, 8, 8, 8, 8, 8, 4, 4, 4, 8, 8, 8, 8, 8, 8, 4, 4, 4, 8, 8, 8, 8, 8, 8, 4, 4, 4, 8, 8, 8, 8, 8, 8, 3, 4, 4, 3, 48, 48, 3, 48, 48, 3, 4, 4, 3, 1098, 1101, 3, 1101, 1098, 3, 4, 4, 3, 1114, 1117, 3, 1117, 1114, 4, 4, 4, 48, 48, 48, 48, 48, 48, 4, 4, 4, 865, 960, 963, 877, 1012, 1015, 4, 4, 4, 850, 1012, 1015, 862, 960, 963, 4, 4, 4, 48, 48, 48, 48, 48, 48, 4, 4, 4, 850, 963, 960, 862, 1015, 1012, 4, 4, 4, 865, 1015, 1012, 877, 963, 960, 3, 4, 4, 3, 48, 48, 3, 48, 48, 3, 4]

theorem obstructionChunk063 (code : Fin 19683)
    (_hlo : 8064 ≤ code.val) (hhi : code.val < 8192) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (8064 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 8064, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 8064 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
