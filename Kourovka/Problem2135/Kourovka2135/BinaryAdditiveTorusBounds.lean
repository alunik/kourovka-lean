import Kourovka2135.BinaryAdditiveTorusCoordinates
import Kourovka2135.BinaryCochainTorusBounds

/-! Fixed-space bounds on ordinary additive-group cohomology for the actual
coefficient representation. The chain comparison, coordinate injection, and
weight arithmetic are all proved; no cohomology bound is an input.
-/
set_option autoImplicit false
noncomputable section
universe u
namespace Kourovka2135.BinaryAdditiveTorusBounds
open CategoryTheory BinaryAdditiveCohomology BinaryAdditiveTorusAction
open BinaryCochainGraded
variable (k : Type u) [Field k] [CharP k 2] {f : ℕ} (I : Finset (Fin f))
variable {F : Type u} [Field F] [Fintype F] (σ : F →+* k)
variable (hcard : Fintype.card F = 2 ^ f)

/-- Ordinary cohomology coordinates using the action-compatible direct comparison. -/
def coordinate (n : ℕ) :
    groupCohomology (coefficientRepresentation k I σ hcard) (n + 1) →ₗ[k]
      (SurvivorIndex I (n + 1) → k) :=
  (BinaryCochainDimension.homologyCoordinate k I n).comp
    (BinaryAdditiveTorusAction.groupCohomologyIso k I σ hcard (n + 1)).hom.hom

theorem coordinate_injective (n : ℕ) : Function.Injective (coordinate k I σ hcard n) :=
  (BinaryCochainDimension.homologyCoordinate_injective k I n).comp
    (BinaryAdditiveTorusAction.groupCohomologyIso k I σ hcard (n + 1)).toLinearEquiv.injective

/-- The coordinates intertwine the actual ordinary group-cohomology map. -/
theorem coordinate_cohomologyMap (r : Fˣ) (n : ℕ)
    (v : groupCohomology (coefficientRepresentation k I σ hcard) (n + 1))
    (a : SurvivorIndex I (n + 1)) :
    coordinate k I σ hcard n ((cohomologyMap k I σ hcard r (n + 1)).hom v) a =
      BinaryTorusFixedCoordinates.character k I (Units.map σ.toMonoidHom r) (n + 1) a *
        coordinate k I σ hcard n v a := by
  have h := congrArg (fun p => p.hom v)
    (BinaryAdditiveTorusCoordinates.groupCohomologyIso_naturality k I σ hcard r (n + 1))
  change BinaryCochainTorusBounds.torusAction k I (Units.map σ.toMonoidHom r) (n + 1)
      ((BinaryAdditiveTorusAction.groupCohomologyIso k I σ hcard (n + 1)).hom.hom v) =
    (BinaryAdditiveTorusAction.groupCohomologyIso k I σ hcard (n + 1)).hom.hom
      ((cohomologyMap k I σ hcard r (n + 1)).hom v) at h
  change BinaryCochainDimension.homologyCoordinate k I n
      ((BinaryAdditiveTorusAction.groupCohomologyIso k I σ hcard (n + 1)).hom.hom
        ((cohomologyMap k I σ hcard r (n + 1)).hom v)) a = _
  rw [← h]
  exact BinaryCochainTorusBounds.homologyCoordinate_torusAction k I
    (Units.map σ.toMonoidHom r) n _ a

/-- The actual torus-fixed H1 subspace has dimension at most one. -/
theorem finrank_fixed_one_le (r : Fˣ)
    (hr : orderOf (Units.map σ.toMonoidHom r) = 2 ^ f - 1) (hf : 2 ≤ f) :
    Module.finrank k ((cohomologyMap k I σ hcard r 1).hom - LinearMap.id).ker ≤ 1 :=
  BinaryTorusFixedCoordinates.finrank_fixed_one_le k I (Units.map σ.toMonoidHom r) hr hf
    (cohomologyMap k I σ hcard r 1).hom (coordinate k I σ hcard 0)
    (coordinate_injective k I σ hcard 0) (coordinate_cohomologyMap k I σ hcard r 0)

/-- Nonsingleton coefficient supports have zero torus-fixed ordinary H1. -/
theorem fixed_one_eq_bot (r : Fˣ)
    (hr : orderOf (Units.map σ.toMonoidHom r) = 2 ^ f - 1) (hf : 2 ≤ f)
    (hI : I.card ≠ 1) :
    ((cohomologyMap k I σ hcard r 1).hom - LinearMap.id).ker = ⊥ :=
  BinaryTorusFixedCoordinates.fixed_one_eq_bot k I (Units.map σ.toMonoidHom r) hr hf hI
    (cohomologyMap k I σ hcard r 1).hom (coordinate k I σ hcard 0)
    (coordinate_injective k I σ hcard 0) (coordinate_cohomologyMap k I σ hcard r 0)

/-- Natural coefficients have at most one fixed ordinary H2 class for f ≥ 3. -/
theorem finrank_fixed_two_le (r : Fˣ)
    (hr : orderOf (Units.map σ.toMonoidHom r) = 2 ^ f - 1) (hf : 3 ≤ f) (i : Fin f) :
    Module.finrank k ((cohomologyMap k {i} σ hcard r 2).hom - LinearMap.id).ker ≤ 1 :=
  BinaryTorusFixedCoordinates.finrank_fixed_two_le k (Units.map σ.toMonoidHom r) hr hf i
    (cohomologyMap k {i} σ hcard r 2).hom (coordinate k {i} σ hcard 1)
    (coordinate_injective k {i} σ hcard 1) (coordinate_cohomologyMap k {i} σ hcard r 1)

/-- Over four parameters the natural coefficient has no fixed ordinary H2 class. -/
theorem fixed_two_at_two_eq_bot (hcard₂ : Fintype.card F = 2 ^ 2) (r : Fˣ)
    (hr : orderOf (Units.map σ.toMonoidHom r) = 2 ^ 2 - 1) (i : Fin 2) :
    ((cohomologyMap k {i} σ hcard₂ r 2).hom - LinearMap.id).ker = ⊥ :=
  BinaryTorusFixedCoordinates.fixed_two_at_two_eq_bot k (Units.map σ.toMonoidHom r) hr i
    (cohomologyMap k {i} σ hcard₂ r 2).hom (coordinate k {i} σ hcard₂ 1)
    (coordinate_injective k {i} σ hcard₂ 1) (coordinate_cohomologyMap k {i} σ hcard₂ r 1)

omit [CharP k 2] in
include hcard in
/-- The primitive unit required by the bounds exists in the actual parameter field. -/
theorem exists_primitive : ∃ r : Fˣ, orderOf (Units.map σ.toMonoidHom r) = 2 ^ f - 1 :=
  BinaryTorusCharacterWeights.exists_primitive_image σ hcard

end Kourovka2135.BinaryAdditiveTorusBounds
