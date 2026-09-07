import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[3, 1058, 1073, 3, 1058, 1073, 3, 1058, 1073, 3, 1073, 1058, 3, 1073, 1058, 3, 1073, 1058, 16, 16, 16, 16, 16, 16, 16, 16, 16, 596, 596, 596, 679, 763, 2143, 675, 2080, 766, 576, 576, 576, 694, 715, 2195, 690, 1360, 718, 16, 16, 16, 16, 16, 16, 16, 16, 16, 598, 598, 598, 644, 2143, 752, 640, 757, 2095, 578, 578, 578, 661, 2176, 704, 657, 709, 1361, 3, 12, 12, 3, 16, 16, 3, 16, 16, 3, 12, 12, 3, 32, 32, 3, 32, 32, 3, 12, 12, 3, 32, 32, 3, 32, 32, 12, 12, 12, 16, 16, 16, 16, 16, 16, 12, 12, 12, 32, 32, 32, 32, 32, 32, 12, 12, 12, 32, 32, 32, 32, 32, 32, 12, 12]

theorem obstructionChunk045 (code : Fin 19683)
    (_hlo : 5760 ≤ code.val) (hhi : code.val < 5888) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (5760 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 5760, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 5760 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
