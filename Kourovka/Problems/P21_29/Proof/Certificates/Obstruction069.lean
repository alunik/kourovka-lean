import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 48, 48, 1, 48, 48, 1, 48, 48, 1, 1024, 1073, 1, 1024, 1073, 1, 1024, 1073, 1, 1073, 1024, 1, 1073, 1024, 1, 1073, 1024, 1, 48, 48, 1, 48, 48, 1, 48, 48, 1, 1058, 1043, 1, 1058, 1043, 1, 1058, 1043, 1, 1043, 1058, 1, 1043, 1058, 1, 1043, 1058, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 48, 48, 1, 48, 48, 1, 48, 48, 1, 1032, 1081, 1, 1032, 1081, 1, 1032, 1081, 1, 1081, 1032, 1, 1081]

theorem obstructionChunk069 (code : Fin 19683)
    (_hlo : 8832 ≤ code.val) (hhi : code.val < 8960) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (8832 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 8832, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 8832 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
