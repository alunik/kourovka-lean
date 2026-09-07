import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[48, 48, 12, 12, 12, 578, 578, 578, 622, 622, 622, 12, 12, 12, 634, 634, 634, 598, 598, 598, 12, 12, 12, 48, 48, 48, 48, 48, 48, 12, 12, 12, 576, 576, 576, 620, 620, 620, 12, 12, 12, 632, 632, 632, 596, 596, 596, 3, 48, 48, 3, 48, 48, 3, 48, 48, 3, 769, 768, 3, 690, 657, 3, 694, 661, 3, 829, 828, 3, 640, 675, 3, 644, 679, 48, 48, 48, 48, 48, 48, 48, 48, 48, 1101, 769, 768, 865, 1156, 1101, 877, 1101, 1160, 1117, 829, 828, 850, 1156, 1117, 862, 1117, 1160, 48, 48, 48, 48, 48, 48, 48, 48, 48, 1098, 769, 768, 850, 1098, 1156, 862, 1160, 1098, 1114, 829, 828, 865, 1114, 1156, 877, 1160, 1114]

theorem obstructionChunk080 (code : Fin 19683)
    (_hlo : 10240 ≤ code.val) (hhi : code.val < 10368) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (10240 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 10240, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 10240 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
