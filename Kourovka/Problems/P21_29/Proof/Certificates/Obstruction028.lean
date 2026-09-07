import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[1066, 3, 1081, 1066, 3, 1081, 1066, 16, 16, 16, 16, 16, 16, 16, 16, 16, 576, 576, 576, 675, 1156, 763, 679, 766, 1748, 596, 596, 596, 690, 1156, 715, 694, 718, 2017, 16, 16, 16, 16, 16, 16, 16, 16, 16, 578, 578, 578, 640, 752, 1156, 644, 1750, 757, 598, 598, 598, 657, 704, 1156, 661, 2002, 709, 3, 12, 12, 3, 16, 16, 3, 16, 16, 3, 12, 12, 3, 32, 32, 3, 32, 32, 3, 12, 12, 3, 32, 32, 3, 32, 32, 12, 12, 12, 16, 16, 16, 16, 16, 16, 12, 12, 12, 32, 32, 32, 32, 32, 32, 12, 12, 12, 32, 32, 32, 32, 32, 32, 12, 12, 12, 16, 16, 16, 16, 16, 16, 12, 12, 12, 32]

theorem obstructionChunk028 (code : Fin 19683)
    (_hlo : 3584 ≤ code.val) (hhi : code.val < 3712) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (3584 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 3584, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 3584 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
