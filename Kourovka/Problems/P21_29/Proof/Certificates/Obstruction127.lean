import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[48, 48, 48, 48, 48, 48, 48, 1114, 792, 793, 862, 1114, 1156, 850, 1786, 1114, 1098, 804, 805, 877, 1098, 1156, 865, 2035, 1098, 3, 12, 12, 3, 792, 793, 3, 804, 805, 3, 12, 12, 3, 704, 715, 3, 718, 709, 3, 12, 12, 3, 752, 763, 3, 766, 757, 12, 12, 12, 928, 792, 793, 943, 804, 805, 12, 12, 12, 928, 1156, 640, 943, 1200, 644, 12, 12, 12, 928, 657, 1156, 943, 661, 2155, 12, 12, 12, 943, 792, 793, 928, 804, 805, 12, 12, 12, 943, 675, 1156, 928, 679, 1200, 12, 12, 12, 943, 1156, 690, 928, 2155, 694, 3, 928, 943, 3, 850, 865, 3, 862, 877, 3, 928, 943, 3, 1156, 1156, 3, 804, 805, 3, 928, 943, 3]

theorem obstructionChunk127 (code : Fin 19683)
    (_hlo : 16256 ≤ code.val) (hhi : code.val < 16384) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (16256 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 16256, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 16256 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
