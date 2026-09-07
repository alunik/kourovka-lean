import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[12, 12, 12, 905, 805, 804, 902, 793, 792, 12, 12, 12, 905, 1156, 690, 902, 1786, 694, 12, 12, 12, 905, 675, 1156, 902, 679, 2029, 12, 12, 12, 902, 805, 804, 905, 793, 792, 12, 12, 12, 902, 657, 1156, 905, 661, 1784, 12, 12, 12, 902, 1156, 640, 905, 2014, 644, 3, 902, 905, 3, 883, 832, 3, 895, 844, 3, 902, 905, 3, 805, 804, 3, 1160, 1160, 3, 902, 905, 3, 1156, 1156, 3, 793, 792, 1043, 1000, 1003, 1043, 1156, 905, 1043, 902, 1160, 1117, 1160, 1043, 622, 241, 100, 1160, 253, 254, 1101, 1043, 1160, 1156, 193, 194, 634, 103, 206, 1024, 1003, 1000, 1024, 902, 1156, 1024, 1160, 905, 1114, 1024, 1160, 620, 107, 240, 1160, 255, 252, 1098, 1160]

theorem obstructionChunk135 (code : Fin 19683)
    (_hlo : 17280 ≤ code.val) (hhi : code.val < 17408) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (17280 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 17280, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 17280 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
