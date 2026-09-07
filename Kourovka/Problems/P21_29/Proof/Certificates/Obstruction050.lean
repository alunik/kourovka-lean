import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[16, 16, 3, 16, 16, 3, 16, 16, 3, 1032, 1051, 3, 1032, 1051, 3, 1032, 1051, 3, 1051, 1032, 3, 1051, 1032, 3, 1051, 1032, 16, 16, 16, 16, 16, 16, 16, 16, 16, 634, 634, 634, 694, 757, 1164, 690, 1945, 752, 622, 622, 622, 679, 709, 1164, 675, 1809, 704, 16, 16, 16, 16, 16, 16, 16, 16, 16, 632, 632, 632, 661, 1164, 766, 657, 763, 1944, 620, 620, 620, 644, 1164, 718, 640, 715, 1842, 3, 16, 16, 3, 16, 16, 3, 16, 16, 3, 1024, 1043, 3, 1024, 1043, 3, 1024, 1043, 3, 1043, 1024, 3, 1043, 1024, 3, 1043, 1024, 16, 16, 16, 16, 16, 16, 16, 16, 16, 598, 598, 598, 694, 2140, 766, 690, 763, 2089, 578, 578, 578]

theorem obstructionChunk050 (code : Fin 19683)
    (_hlo : 6400 ≤ code.val) (hhi : code.val < 6528) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (6400 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 6400, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 6400 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
