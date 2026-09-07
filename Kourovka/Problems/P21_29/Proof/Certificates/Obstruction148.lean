import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[241, 1101, 1073, 1357, 2247, 206, 205, 578, 69, 193, 3, 12, 12, 3, 48, 48, 3, 48, 48, 3, 12, 12, 3, 661, 694, 3, 657, 690, 3, 12, 12, 3, 679, 644, 3, 675, 640, 12, 12, 12, 48, 48, 48, 48, 48, 48, 12, 12, 12, 598, 598, 598, 634, 634, 634, 12, 12, 12, 622, 622, 622, 578, 578, 578, 12, 12, 12, 48, 48, 48, 48, 48, 48, 12, 12, 12, 596, 596, 596, 632, 632, 632, 12, 12, 12, 620, 620, 620, 576, 576, 576, 3, 48, 48, 3, 48, 48, 3, 48, 48, 3, 769, 768, 3, 661, 694, 3, 657, 690, 3, 829, 828, 3, 679, 644, 3, 675, 640, 48, 48, 48, 48, 48, 48, 48, 48, 48, 1114]

theorem obstructionChunk148 (code : Fin 19683)
    (_hlo : 18944 ≤ code.val) (hhi : code.val < 19072) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (18944 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 18944, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 18944 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
