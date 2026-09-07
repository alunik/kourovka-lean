import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 960, 963, 1, 694, 679, 1, 690, 675, 1, 757, 752, 1, 960, 963, 1, 1168, 1168, 1, 709, 704, 1, 1164, 1164, 1, 960, 963, 1, 963, 960, 1, 644, 661, 1, 640, 657, 1, 763, 766, 1, 963, 960, 1, 1168, 1168, 1, 715, 718, 1, 1164, 1164, 1, 963, 960, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 988, 991, 1, 694, 679, 1, 690, 675, 1, 763, 766, 1, 1168, 1168, 1, 988, 991, 1, 715, 718, 1, 988, 991, 1, 1984, 2017, 1, 991, 988, 1, 644, 661, 1, 640, 657, 1, 757]

theorem obstructionChunk090 (code : Fin 19683)
    (_hlo : 11520 ≤ code.val) (hhi : code.val < 11648) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (11520 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 11520, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 11520 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
