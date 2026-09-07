import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[832, 1117, 1915, 3, 12, 12, 3, 792, 793, 3, 804, 805, 3, 12, 12, 3, 715, 704, 3, 709, 718, 3, 12, 12, 3, 763, 752, 3, 757, 766, 12, 12, 12, 905, 792, 793, 902, 804, 805, 12, 12, 12, 905, 644, 1168, 902, 640, 1168, 12, 12, 12, 905, 1184, 661, 902, 1184, 657, 12, 12, 12, 902, 792, 793, 905, 804, 805, 12, 12, 12, 902, 1168, 679, 905, 1168, 675, 12, 12, 12, 902, 694, 1184, 905, 690, 1184, 3, 902, 905, 3, 832, 883, 3, 844, 895, 3, 902, 905, 3, 1164, 1164, 3, 804, 805, 3, 902, 905, 3, 792, 793, 3, 1184, 1184, 1032, 1012, 1015, 1032, 1164, 905, 1032, 902, 1184, 1095, 1032, 1168, 1164, 196, 199, 596, 84]

theorem obstructionChunk093 (code : Fin 19683)
    (_hlo : 11904 ≤ code.val) (hhi : code.val < 12032) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (11904 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 11904, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 11904 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
