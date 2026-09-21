import Kourovka2135.GroupCohomologyFieldExtension

/-! Actual moving ranks are unchanged under extension of the coefficient
field. Kernel transport and rank-nullity compare the concrete linear maps.
-/

set_option autoImplicit false
noncomputable section
universe u

namespace Kourovka2135.RepresentationBaseChangeMovingRank

open TensorProduct RepresentationDensityBaseChange

variable {E L : Type u} [Field E] [Field L] [Algebra E L]
variable {V W : Type u} [AddCommGroup V] [Module E V]
variable [AddCommGroup W] [Module E W] [FiniteDimensional E V]

/-- Field extension preserves the rank of the actual scalar-extended map. -/
theorem finrank_range_baseChange (f : V →ₗ[E] W) :
    Module.finrank L (LinearMap.range (f.baseChange L)) =
      Module.finrank E (LinearMap.range f) := by
  have hE := f.finrank_range_add_finrank_ker
  have hL := (f.baseChange L).finrank_range_add_finrank_ker
  rw [GroupCohomologyFieldExtension.finrank_ker_baseChange,
    Module.finrank_baseChange] at hL
  omega

variable {G : Type u} [Monoid G]

omit [FiniteDimensional E V] in
/-- The moving operator is exactly the scalar extension of the original one. -/
theorem moving_operator (ρ : Representation E G V) (g : G) :
    baseChange L ρ g - LinearMap.id = (ρ g - LinearMap.id).baseChange L := by
  rw [LinearMap.baseChange_sub, LinearMap.baseChange_id, baseChange_apply]

/-- The rank moved by an actual group element is unchanged after field extension. -/
theorem finrank_moving_baseChange (ρ : Representation E G V) (g : G) :
    Module.finrank L (baseChange L ρ g - LinearMap.id).range =
      Module.finrank E (ρ g - LinearMap.id).range := by
  rw [moving_operator]
  exact finrank_range_baseChange _

end Kourovka2135.RepresentationBaseChangeMovingRank
