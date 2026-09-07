import Kourovka.Problems.P21_29.Proof.FiniteModel

/-! Generated witnesses; the assertions below are kernel-checked. -/

namespace Kourovka.P21_29

private def witnesses : Array ℕ := #[763, 752, 3, 12, 12, 3, 709, 718, 3, 715, 704, 12, 12, 12, 896, 829, 828, 911, 769, 768, 12, 12, 12, 896, 2140, 694, 911, 2057, 690, 12, 12, 12, 896, 679, 2233, 911, 675, 1354, 12, 12, 12, 911, 829, 828, 896, 769, 768, 12, 12, 12, 911, 661, 2140, 896, 657, 2054, 12, 12, 12, 911, 2218, 644, 896, 1355, 640, 3, 896, 911, 3, 883, 832, 3, 895, 844, 3, 896, 911, 3, 1164, 1164, 3, 769, 768, 3, 896, 911, 3, 829, 828, 3, 1870, 1861, 1051, 988, 991, 1051, 896, 1164, 1051, 1792, 911, 1114, 1981, 1051, 1164, 245, 246, 634, 249, 112, 1098, 1051, 1813, 622, 115, 198, 2057, 201, 202, 1032, 991, 988, 1032, 1164, 911, 1032, 896, 1827]

theorem obstructionChunk152 (code : Fin 19683)
    (_hlo : 19456 ≤ code.val) (hhi : code.val < 19584) :
    ∃ w : ℕ, obstructionCheck code.val w = true := by
  have h : ∀ i : Fin 128,
      obstructionCheck (19456 + i.val) witnesses[i.val]! = true := by
    decide +kernel
  let i : Fin 128 := ⟨code.val - 19456, by omega⟩
  refine ⟨witnesses[i.val]!, ?_⟩
  have hi := h i
  have heq : 19456 + i.val = code.val := by dsimp [i]; omega
  simpa only [heq] using hi

end Kourovka.P21_29
