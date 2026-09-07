import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[3, 793, 792, 3, 943, 928, 3, 805, 804, 3, 2210, 2225, 1024, 988, 991, 1024, 1750, 928, 1024, 943, 1909, 1095, 1024, 1168, 1168, 237, 238, 598, 92, 226, 1111, 1856, 1024, 578, 221, 95, 1809, 209, 210, 1043, 991, 988, 1043, 943, 1748, 1043, 1918, 928, 1088, 1168, 1043, 1168, 239, 236, 596, 227, 83, 1104, 1043, 1867, 576, 80, 220, 1842, 211, 208, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 4, 4, 1, 8, 8, 1, 8, 8, 1, 4, 4, 1, 8, 8, 1, 8, 8, 1, 4, 4, 1, 8, 8, 1, 8, 8, 1, 4, 4, 1, 8, 8, 1, 8]

theorem obstructionChunk102 (code : Fin 19683)
    (_hlo : 13056 ≤ code.val) (hhi : code.val < 13184) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (13056 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 13056, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 13056 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
