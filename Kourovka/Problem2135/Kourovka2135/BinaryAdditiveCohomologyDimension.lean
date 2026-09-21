import Kourovka2135.BinaryAdditiveCohomology
import Kourovka2135.BinaryCochainDimension

/-! Ordinary positive-degree group cohomology is detected by actual surviving
monomial coordinates. The resulting dimension bound has no cohomological
vanishing, exactness, finite-dimensionality, or classification premise. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Kourovka2135.BinaryAdditiveCohomologyDimension
open BinaryAdditiveCohomology BinaryCochainGraded
variable (k : Type u) [Field k] [CharP k 2] {f : ℕ} (I : Finset (Fin f))
variable {F : Type u} [Field F] [Fintype F] (σ : F →+* k)
variable (hcard : Fintype.card F = 2 ^ f)

/-- Actual monomial coordinates on ordinary group cohomology. -/
def coordinates (n : ℕ) :
    groupCohomology (coefficientRepresentation k I σ hcard) (n + 1) →ₗ[k]
      (SurvivorIndex I (n + 1) → k) :=
  (BinaryCochainDimension.homologyCoordinate k I n).comp
    (groupCohomologyIso k I σ hcard (n + 1)).hom.hom

theorem coordinates_injective (n : ℕ) : Function.Injective (coordinates k I σ hcard n) :=
  (BinaryCochainDimension.homologyCoordinate_injective k I n).comp
    (groupCohomologyIso k I σ hcard (n + 1)).toLinearEquiv.injective

/-- Finiteness of ordinary group cohomology follows from its explicit coordinate injection. -/
theorem finiteDimensional_groupCohomology (n : ℕ) :
    FiniteDimensional k (groupCohomology (coefficientRepresentation k I σ hcard) (n + 1)) :=
  FiniteDimensional.of_injective (coordinates k I σ hcard n)
    (coordinates_injective k I σ hcard n)

/-- Ordinary group cohomology is bounded by the outside exponent monomials. -/
theorem finrank_groupCohomology_le (n : ℕ) :
    Module.finrank k (groupCohomology (coefficientRepresentation k I σ hcard) (n + 1)) ≤
      Fintype.card (SurvivorIndex I (n + 1)) := by
  calc
    Module.finrank k (groupCohomology (coefficientRepresentation k I σ hcard) (n + 1)) ≤
        Module.finrank k (SurvivorIndex I (n + 1) → k) :=
      LinearMap.finrank_le_finrank_of_injective (coordinates_injective k I σ hcard n)
    _ = Fintype.card (SurvivorIndex I (n + 1)) := Module.finrank_fintype_fun_eq_card k

end Kourovka2135.BinaryAdditiveCohomologyDimension
