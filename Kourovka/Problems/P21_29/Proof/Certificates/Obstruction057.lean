import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[3, 8, 8, 3, 4, 4, 3, 8, 8, 3, 8, 8, 3, 4, 4, 3, 8, 8, 3, 8, 8, 4, 4, 4, 8, 8, 8, 8, 8, 8, 4, 4, 4, 8, 8, 8, 8, 8, 8, 4, 4, 4, 8, 8, 8, 8, 8, 8, 4, 4, 4, 8, 8, 8, 8, 8, 8, 4, 4, 4, 8, 8, 8, 8, 8, 8, 4, 4, 4, 8, 8, 8, 8, 8, 8, 3, 4, 4, 3, 48, 48, 3, 48, 48, 3, 4, 4, 3, 1088, 1095, 3, 1095, 1088, 3, 4, 4, 3, 1104, 1111, 3, 1111, 1104, 4, 4, 4, 48, 48, 48, 48, 48, 48, 4, 4, 4, 832, 960, 963, 844, 1012, 1015, 4, 4, 4, 883, 1012, 1015, 895, 960]

theorem obstructionChunk057 (code : Fin 19683)
    (_hlo : 7296 ≤ code.val) (hhi : code.val < 7424) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (7296 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 7296, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 7296 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
