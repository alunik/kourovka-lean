import Kourovka.Problem2153.RankOne.Cells.Metadata
import Kourovka.Problem2153.RankOne.Basic

set_option autoImplicit false
set_option Elab.async false

namespace Kourovka.Problem2153.RootSystem.RankOne

theorem r_lhs_spec : ∀ k : Fin 63, r_lhs k =
    [.rho, .root 1 (rInput k).1, .root 3 (rInput k).2, .rho] := by decide +kernel

theorem r_rhs_spec : ∀ k : Fin 63, r_rhs k =
    [.root 1 (rLeft k).1, .root 3 (rLeft k).2,
      .torus (rTorus k).1 (rTorus k).2, .rho,
      .root 1 (rRight k).1, .root 3 (rRight k).2] := by decide +kernel

theorem s_lhs_spec : ∀ k : Fin 7, s_lhs k = [.sigma, .root 0 (sInput k), .sigma] := by
  decide +kernel

theorem s_rhs_spec : ∀ k : Fin 7, s_rhs k =
    [.root 0 (sLeft k), .torus (sTorus k).1 (sTorus k).2, .sigma,
      .root 0 (sRight k)] := by decide +kernel

theorem r_input_coverage : ∀ p : Fin 8 × Fin 8, p ≠ (0, 0) → ∃ k, rInput k = p := by
  decide +kernel

theorem s_input_coverage : ∀ a : Fin 8, a ≠ 0 → ∃ k, sInput k = a := by decide +kernel

end Kourovka.Problem2153.RootSystem.RankOne
