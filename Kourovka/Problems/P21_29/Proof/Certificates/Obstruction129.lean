import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[1200, 214, 213, 1098, 2167, 1032, 1156, 234, 233, 634, 230, 96, 3, 12, 12, 3, 804, 805, 3, 792, 793, 3, 12, 12, 3, 752, 763, 3, 766, 757, 3, 12, 12, 3, 704, 715, 3, 718, 709, 12, 12, 12, 896, 804, 805, 911, 792, 793, 12, 12, 12, 896, 675, 1156, 911, 679, 1784, 12, 12, 12, 896, 1156, 690, 911, 1996, 694, 12, 12, 12, 911, 804, 805, 896, 792, 793, 12, 12, 12, 911, 1156, 640, 896, 1786, 644, 12, 12, 12, 911, 657, 1156, 896, 661, 2047, 3, 896, 911, 3, 865, 850, 3, 877, 862, 3, 896, 911, 3, 804, 805, 3, 1160, 1160, 3, 896, 911, 3, 1156, 1156, 3, 792, 793, 1058, 1000, 1003, 1058, 896, 1156, 1058, 1160]

theorem obstructionChunk129 (code : Fin 19683)
    (_hlo : 16512 ≤ code.val) (hhi : code.val < 16640) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (16512 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 16512, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 16512 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
