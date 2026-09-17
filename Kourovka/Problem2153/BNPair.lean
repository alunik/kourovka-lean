import Kourovka.Problem2153.BNPair.Construction
import Kourovka.Problem2153.UnipotentFactorization

set_option autoImplicit false

namespace Kourovka.Problem2153.RootSystem.BNPair

/-- The Tits system of the explicit matrix group. Every structural premise is proved. -/
def concrete : TauCeti.TitsSystem G := of_factorizations U_factor_r U_factor_s

/-- Every element of the actual matrix group has a U H W U decomposition. -/
theorem uhwu_coverage :
    BruhatCoverage (fun u : U => (u : G)) (fun h : H => (h : G)) Weyl.rep :=
  uhwu_of_factorizations U_factor_r U_factor_s

/-- B W B coverage in the exact form used by the simplicity argument. -/
theorem coverage (g : G) :
    ∃ b₁ ∈ B, ∃ k : Fin 16, ∃ b₂ ∈ B, g = b₁ * Weyl.rep k * b₂ := by
  obtain ⟨u,h,k,v,he⟩ := uhwu_coverage g
  exact ⟨(u : G) * (h : G),
    B.mul_mem ((show U ≤ B from le_sup_left) u.property)
      ((show H ≤ B from le_sup_right) h.property), k, v,
    (show U ≤ B from le_sup_left) v.property, he⟩

#print axioms uhwu_coverage
#print axioms coverage

end Kourovka.Problem2153.RootSystem.BNPair
