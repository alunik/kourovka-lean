import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[963, 4, 4, 4, 48, 48, 48, 48, 48, 48, 4, 4, 4, 883, 963, 960, 895, 1015, 1012, 4, 4, 4, 832, 1015, 1012, 844, 963, 960, 3, 4, 4, 3, 48, 48, 3, 48, 48, 3, 4, 4, 3, 1098, 1101, 3, 1101, 1098, 3, 4, 4, 3, 1114, 1117, 3, 1117, 1114, 4, 4, 4, 48, 48, 48, 48, 48, 48, 4, 4, 4, 844, 1000, 1003, 832, 988, 991, 4, 4, 4, 895, 988, 991, 883, 1000, 1003, 4, 4, 4, 48, 48, 48, 48, 48, 48, 4, 4, 4, 895, 1003, 1000, 883, 991, 988, 4, 4, 4, 844, 991, 988, 832, 1003, 1000, 3, 4, 4, 3, 8, 8, 3, 8, 8, 3, 4, 4, 3, 8, 8, 3, 8, 8, 3]

theorem obstructionChunk058 (code : Fin 19683)
    (_hlo : 7424 ≤ code.val) (hhi : code.val < 7552) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (7424 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 7424, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 7424 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
