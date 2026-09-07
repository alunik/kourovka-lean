import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[1024, 1156, 195, 192, 632, 207, 104, 3, 905, 902, 3, 895, 844, 3, 883, 832, 3, 905, 902, 3, 1156, 1156, 3, 793, 792, 3, 905, 902, 3, 805, 804, 3, 2250, 2253, 1051, 1012, 1015, 1051, 905, 1156, 1051, 2002, 902, 1104, 1750, 1051, 1156, 249, 250, 578, 245, 88, 1088, 1051, 2029, 598, 91, 202, 1861, 197, 198, 1032, 1015, 1012, 1032, 1156, 902, 1032, 905, 2017, 1111, 1032, 1748, 1156, 251, 248, 576, 87, 244, 1095, 2014, 1032, 596, 203, 84, 1870, 199, 196, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 12, 12, 1, 48, 48, 1, 48, 48, 1, 12, 12, 1]

theorem obstructionChunk136 (code : Fin 19683)
    (_hlo : 17408 ≤ code.val) (hhi : code.val < 17536) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (17408 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 17408, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 17408 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
