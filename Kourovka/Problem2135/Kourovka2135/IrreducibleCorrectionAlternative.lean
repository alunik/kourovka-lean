import Kourovka2135.IrreducibleEndCohomology

/-! Descent of the two sufficient alternatives for the minimal-kernel
correction argument. The equality between dual and original H1 dimensions
is an explicit input, later supplied by the actual commutator pairing. -/

set_option autoImplicit false
noncomputable section
universe u

namespace Kourovka2135.IrreducibleCorrectionAlternative
open IrreducibleEndCohomology

variable {K G V : Type u} [Field K] [Group G] [Finite G]
variable [AddCommGroup V] [Module K V] [Finite V]
variable (ρ : Representation K G V) [ρ.IsIrreducible]

/-- The common commuting-field degree cancels in both alternatives.
Finite-dimensionality of dual cohomology is proved before using its rank. -/
theorem descend (g : G)
    (hdual : Module.finrank K (groupCohomology (Rep.of ρ.dual) 1) =
      Module.finrank K (groupCohomology (Rep.of ρ) 1))
    (hclosed :
      Module.finrank (ClosedField ρ) (groupCohomology (Rep.of (extended ρ)) 1) = 0 ∨
        (Module.finrank (ClosedField ρ) (groupCohomology (Rep.of (extended ρ)) 1) ≤ 1 ∧
          4 ≤ Module.finrank (ClosedField ρ)
            (LinearMap.range (extended ρ g - LinearMap.id)))) :
    Subsingleton (groupCohomology (Rep.of ρ.dual) 1) ∨
      2 * Module.finrank K (ρ.IntertwiningMap ρ) +
        2 * Module.finrank K (groupCohomology (Rep.of ρ.dual) 1) ≤
          Module.finrank K (LinearMap.range (ρ g - LinearMap.id)) := by
  rcases hclosed with hz | ⟨hH, hm⟩
  · left
    let : FiniteDimensional K (groupCohomology (Rep.of ρ.dual) 1) :=
      GroupCohomologyFieldExtension.finiteDimensional_groupCohomology ρ.dual 0
    apply (Module.finrank_zero_iff (R := K)
      (M := groupCohomology (Rep.of ρ.dual) 1)).mp
    rw [hdual, finrank_cohomology_eq_closed ρ 0, hz, mul_zero]
  · exact Or.inr (correction_rank_bound ρ g hH hm hdual)

end Kourovka2135.IrreducibleCorrectionAlternative
