import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[12, 905, 640, 1156, 902, 644, 1184, 12, 12, 12, 902, 769, 768, 905, 829, 828, 12, 12, 12, 902, 690, 1156, 905, 694, 1168, 12, 12, 12, 902, 1156, 675, 905, 1184, 679, 3, 902, 905, 3, 850, 865, 3, 862, 877, 3, 902, 905, 3, 769, 768, 3, 1160, 1160, 3, 902, 905, 3, 1156, 1156, 3, 829, 828, 1073, 960, 963, 1073, 1156, 905, 1073, 902, 1160, 1101, 1160, 1073, 578, 193, 69, 1160, 205, 206, 1117, 1073, 1160, 1156, 241, 242, 598, 70, 254, 1058, 963, 960, 1058, 902, 1156, 1058, 1160, 905, 1098, 1058, 1160, 576, 74, 192, 1160, 207, 204, 1114, 1160, 1058, 1156, 243, 240, 596, 255, 73, 3, 905, 902, 3, 862, 877, 3, 850, 865, 3, 905, 902, 3]

theorem obstructionChunk082 (code : Fin 19683)
    (_hlo : 10496 ≤ code.val) (hhi : code.val < 10624) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (10496 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 10496, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 10496 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
