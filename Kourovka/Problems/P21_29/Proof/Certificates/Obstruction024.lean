import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[32, 32, 32, 32, 32, 32, 3, 16, 16, 3, 16, 16, 3, 16, 16, 3, 32, 32, 3, 32, 32, 3, 32, 32, 3, 32, 32, 3, 32, 32, 3, 32, 32, 16, 16, 16, 16, 16, 16, 16, 16, 16, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 16, 16, 16, 16, 16, 16, 16, 16, 16, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 3, 12, 12, 3, 16, 16, 3, 16, 16, 3, 12, 12, 3, 704, 715, 3, 718, 709, 3, 12, 12, 3, 752, 763, 3, 766, 757, 12, 12, 12, 16, 16, 16, 16, 16, 16, 12, 12, 12, 640, 960]

theorem obstructionChunk024 (code : Fin 19683)
    (_hlo : 3072 ≤ code.val) (hhi : code.val < 3200) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (3072 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 3072, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 3072 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
