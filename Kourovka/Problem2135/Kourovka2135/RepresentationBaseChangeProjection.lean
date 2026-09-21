import Kourovka2135.RepresentationDensityBaseChange
import Kourovka2135.GroupCohomologyScalarRestriction
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! Nonzero intertwiners descend by actual tensor coefficient projections.

An E-basis of L identifies L tensor_E V with finitely supported copies of V.
Every coordinate projection commutes with the scalar-extended group action.
Consequently a nonzero k-linear intertwiner into that scalar extension has
an actual nonzero k-linear coefficient intertwiner into V. No finiteness
of L/E, simplicity, or semisimplicity assumption is used.
-/

set_option autoImplicit false
noncomputable section
universe u v

namespace Kourovka2135.RepresentationBaseChangeProjection

open scoped TensorProduct
open RepresentationDensityBaseChange

section Coefficients
variable {E L G V : Type u} [Field E] [Field L] [Algebra E L]
variable [Group G] [AddCommGroup V] [Module E V]
variable {ι : Type v} (b : Module.Basis ι E L)

/-- The actual coefficient of a chosen E-basis vector of L. -/
def projection (i : ι) : (L ⊗[E] V) →ₗ[E] V := by
  classical
  exact (Finsupp.lapply i).comp (TensorProduct.equivFinsuppOfBasisLeft b).toLinearMap

@[simp] theorem projection_tmul (i : ι) (a : L) (v : V) :
    projection b i (a ⊗ₜ[E] v) = b.repr a i • v := by
  classical
  exact TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply b a v i

/-- Coefficient projections separate points of the actual tensor product. -/
theorem exists_projection_ne_zero {z : L ⊗[E] V} (hz : z ≠ 0) :
    ∃ i : ι, projection b i z ≠ 0 := by
  classical
  by_contra! h
  apply hz
  apply (TensorProduct.equivFinsuppOfBasisLeft b).injective
  apply Finsupp.ext
  intro i
  simp only [map_zero, Finsupp.zero_apply]
  exact h i

/-- The group action changes only the second factor, so every coefficient
projection is equivariant for the original E-action. -/
theorem projection_intertwines (ρ : Representation E G V) (i : ι) (g : G)
    (z : L ⊗[E] V) :
    projection b i (baseChange L ρ g z) = ρ g (projection b i z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a v =>
      simp only [baseChange_apply, LinearMap.baseChange_tmul, projection_tmul, map_smul]
  | add z w hz hw => simp only [map_add, hz, hw]

end Coefficients

section Descent
variable (k : Type u) [Field k]
variable {E L G V U : Type u} [Field E] [Field L]
variable [Algebra k E] [Algebra E L] [Algebra k L] [IsScalarTower k E L]
variable [Group G] [AddCommGroup V] [Module E V] [Module k V] [IsScalarTower k E V]
variable [AddCommGroup U] [Module k U]
variable (ρ : Representation E G V) (σ : Representation k G U)
variable {ι : Type v} (b : Module.Basis ι E L)

/-- An actual tensor coefficient as a k-linear intertwining map. -/
def projectionIntertwiner (i : ι) :
    (GroupCohomologyScalarRestriction.restrict k (baseChange L ρ)).IntertwiningMap
      (GroupCohomologyScalarRestriction.restrict k ρ) where
  toLinearMap := (projection b i).restrictScalars k
  isIntertwining' g := by
    apply LinearMap.ext
    intro z
    exact projection_intertwines b ρ i g z

@[simp] theorem projectionIntertwiner_apply (i : ι) (z : L ⊗[E] V) :
    projectionIntertwiner k ρ b i z = projection b i z := rfl

/-- At least one actual coefficient of a nonzero intertwiner is nonzero. -/
theorem exists_projection_comp_ne_zero
    (ψ : σ.IntertwiningMap (GroupCohomologyScalarRestriction.restrict k (baseChange L ρ)))
    (hψ : ψ ≠ 0) :
    ∃ i : ι, (projectionIntertwiner k ρ b i).comp ψ ≠ 0 := by
  classical
  have hu : ∃ u : U, ψ u ≠ 0 := by
    by_contra! h
    apply hψ
    ext u
    exact h u
  obtain ⟨u, hu⟩ := hu
  obtain ⟨i, hi⟩ := exists_projection_ne_zero b hu
  refine ⟨i, ?_⟩
  intro h
  apply hi
  exact congrArg (fun f : σ.IntertwiningMap
    (GroupCohomologyScalarRestriction.restrict k ρ) => f u) h

/-- A nonzero map to a scalar extension yields a genuine nonzero map to the
original representation after restriction to k. No finite extension is assumed. -/
theorem exists_nonzero_intertwiner
    (ψ : σ.IntertwiningMap (GroupCohomologyScalarRestriction.restrict k (baseChange L ρ)))
    (hψ : ψ ≠ 0) :
    ∃ φ : σ.IntertwiningMap (GroupCohomologyScalarRestriction.restrict k ρ), φ ≠ 0 := by
  classical
  obtain ⟨i, hi⟩ := exists_projection_comp_ne_zero k ρ σ
    (Module.Free.chooseBasis E L) ψ hψ
  exact ⟨(projectionIntertwiner k ρ (Module.Free.chooseBasis E L) i).comp ψ, hi⟩

end Descent
end Kourovka2135.RepresentationBaseChangeProjection
