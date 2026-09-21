import Kourovka2135.RepresentationDensityBaseChange
import Kourovka2135.GroupCohomologyFieldExtension
import Kourovka2135.GroupCohomologyScalarRestriction
import Kourovka2135.RepresentationBaseChangeMovingRank
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! Exact ordinary-cohomology and moving-rank descent through the actual
commuting field of an arbitrary finite irreducible representation.
The common field-degree factor is retained, so no identification of that
field with the prime field is needed for the scaled correction inequality. -/

set_option autoImplicit false
noncomputable section
universe u

namespace Kourovka2135.IrreducibleEndCohomology
open MinimalEndMovingRank RepresentationDensityBaseChange
open scoped TensorProduct

variable {K G V : Type u} [Field K] [Group G] [Finite G]
variable [AddCommGroup V] [Module K V] [Finite V]
variable (ρ : Representation K G V) [ρ.IsIrreducible]

abbrev ClosedField := AlgebraicClosure (EndField ρ)
abbrev ExtendedCarrier := ClosedField ρ ⊗[EndField ρ] V

def extended : Representation (ClosedField ρ) G (ExtendedCarrier ρ) :=
  baseChange (ClosedField ρ) (overEnd ρ)

instance extended_isIrreducible : (extended ρ).IsIrreducible :=
  overEnd_baseChange_isIrreducible ρ (ClosedField ρ)

omit [Finite G] in
theorem finrank_extended_coefficient :
    Module.finrank (ClosedField ρ) (ExtendedCarrier ρ) = Module.finrank (EndField ρ) V :=
  Module.finrank_baseChange

omit [Finite G] in
theorem restrict_overEnd : GroupCohomologyScalarRestriction.restrict K (overEnd ρ) = ρ := by
  apply MonoidHom.ext
  intro g
  exact overEnd_restrictScalars ρ g

omit [ρ.IsIrreducible] in
theorem finiteDimensional_cohomology (n : ℕ) :
    FiniteDimensional K (groupCohomology (Rep.of ρ) (n + 1)) :=
  GroupCohomologyFieldExtension.finiteDimensional_groupCohomology ρ n

/-- Exact scalar tower identity on the actual group cohomology. -/
theorem finrank_cohomology_eq_closed (n : ℕ) :
    Module.finrank K (groupCohomology (Rep.of ρ) (n + 1)) =
      Module.finrank K (EndField ρ) *
        Module.finrank (ClosedField ρ) (groupCohomology (Rep.of (extended ρ)) (n + 1)) := by
  have hres := GroupCohomologyScalarRestriction.finrank_groupCohomology_restrict K (overEnd ρ) n
  rw [restrict_overEnd ρ] at hres
  have hbase := GroupCohomologyFieldExtension.finrank_groupCohomology_baseChange
    (L := ClosedField ρ) (overEnd ρ) n
  change Module.finrank (ClosedField ρ) (groupCohomology (Rep.of (extended ρ)) (n + 1)) =
    Module.finrank (EndField ρ) (groupCohomology (Rep.of (overEnd ρ)) (n + 1)) at hbase
  rw [hres, ← hbase]

omit [Finite G] in
/-- The moving rank has exactly the same scalar tower factor. -/
theorem finrank_moving_eq_closed (g : G) :
    Module.finrank K (LinearMap.range (ρ g - LinearMap.id)) =
      Module.finrank K (EndField ρ) *
        Module.finrank (ClosedField ρ) (LinearMap.range (extended ρ g - LinearMap.id)) := by
  have hbase := RepresentationBaseChangeMovingRank.finrank_moving_baseChange
    (L := ClosedField ρ) (overEnd ρ) g
  change Module.finrank (ClosedField ρ)
      (LinearMap.range (extended ρ g - LinearMap.id)) =
    Module.finrank (EndField ρ) (LinearMap.range (overEnd ρ g - LinearMap.id)) at hbase
  exact (moving_finrank_eq ρ g).trans
    (congrArg (fun n => Module.finrank K (EndField ρ) * n) hbase.symm)

theorem finrank_H1_le_endDegree
    (hH : Module.finrank (ClosedField ρ) (groupCohomology (Rep.of (extended ρ)) 1) ≤ 1) :
    Module.finrank K (groupCohomology (Rep.of ρ) 1) ≤ Module.finrank K (EndField ρ) := by
  rw [finrank_cohomology_eq_closed ρ 0]
  simpa only [mul_one] using Nat.mul_le_mul_left (Module.finrank K (EndField ρ)) hH

/-- Four moved dimensions over the closure suffice after retaining the common field degree. -/
theorem correction_rank_bound
    (g : G)
    (hH : Module.finrank (ClosedField ρ) (groupCohomology (Rep.of (extended ρ)) 1) ≤ 1)
    (hmove : 4 ≤ Module.finrank (ClosedField ρ)
      (LinearMap.range (extended ρ g - LinearMap.id)))
    (hdual : Module.finrank K (groupCohomology (Rep.of ρ.dual) 1) =
      Module.finrank K (groupCohomology (Rep.of ρ) 1)) :
    2 * Module.finrank K (ρ.IntertwiningMap ρ) +
      2 * Module.finrank K (groupCohomology (Rep.of ρ.dual) 1) ≤
        Module.finrank K (LinearMap.range (ρ g - LinearMap.id)) := by
  have hcoh := finrank_H1_le_endDegree ρ hH
  have hm := Nat.mul_le_mul_left (Module.finrank K (EndField ρ)) hmove
  rw [← finrank_moving_eq_closed ρ g] at hm
  rw [hdual]
  change 2 * Module.finrank K (EndField ρ) +
      2 * Module.finrank K (groupCohomology (Rep.of ρ) 1) ≤ _
  omega

/-- Actual vanishing also descends, with finite-dimensionality proved independently. -/
theorem subsingleton_H1_of_closed_finrank_eq_zero
    (hH : Module.finrank (ClosedField ρ) (groupCohomology (Rep.of (extended ρ)) 1) = 0) :
    Subsingleton (groupCohomology (Rep.of ρ) 1) := by
  let : FiniteDimensional K (groupCohomology (Rep.of ρ) 1) := finiteDimensional_cohomology ρ 0
  apply (Module.finrank_zero_iff (R := K)
    (M := groupCohomology (Rep.of ρ) 1)).mp
  rw [finrank_cohomology_eq_closed ρ 0, hH, mul_zero]

end Kourovka2135.IrreducibleEndCohomology
