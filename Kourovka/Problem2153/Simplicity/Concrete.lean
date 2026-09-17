import Kourovka.Problem2153.ParabolicMaximal
import Kourovka.Problem2153.NormalGeneration
import Kourovka.Problem2153.NormalGeneration.RootSubgroup

set_option autoImplicit false
namespace Kourovka.Problem2153.RootSystem

/-- All Iwasawa inputs are proved for the actual Wilson matrices. Only the separately
assembled Bruhat coverage is passed in, so no finite simple-group identification is assumed. -/
theorem ambient_isSimpleGroup_of_coverage
    (hCover : ∀ g : G, ∃ b₁ ∈ B, ∃ k : Fin 16, ∃ b₂ ∈ B,
      g = b₁ * Weyl.rep k * b₂) : IsSimpleGroup G :=
  isSimpleGroup_of_iwasawa_subgroups P Z (P_isCoatom_of_coverage hCover)
    P_normalCore P_le_normalizer_Z Z_abelian normalClosure_Z ambient_perfect

#print axioms ambient_isSimpleGroup_of_coverage
end Kourovka.Problem2153.RootSystem
