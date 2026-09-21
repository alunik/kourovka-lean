import Kourovka2135.BinaryCochainTorusComplex
import Kourovka2135.BinaryTorusFixedCoordinates

/-! Low-degree fixed-space bounds on the actual binary cochain homology.

Every equivariance and injectivity premise in the generic coordinate bound
is discharged by the concrete complex and its proved contraction.
-/
set_option autoImplicit false
noncomputable section
namespace Kourovka2135.BinaryCochainTorusBounds
open BinaryCochainComplex BinaryCochainDimension BinaryCochainTorusComplex
variable (k : Type*) [Field k] [CharP k 2] {f : ℕ} (I : Finset (Fin f))

/-- The actual torus action induced on the cohomology of the explicit complex. -/
def torusAction (r : kˣ) (n : ℕ) :
    (complex k I).homology n ≃ₗ[k] (complex k I).homology n :=
  homologyAction k I ((r ^ BinaryTensorTorus.binaryWeight I)⁻¹)
    (BinaryExteriorScaling.torusCoefficients k f r) n

theorem homologyCoordinate_torusAction (r : kˣ) (n : ℕ)
    (v : (complex k I).homology (n + 1))
    (a : BinaryCochainGraded.SurvivorIndex I (n + 1)) :
    homologyCoordinate k I n (torusAction k I r (n + 1) v) a =
      BinaryTorusFixedCoordinates.character k I r (n + 1) a *
        homologyCoordinate k I n v a :=
  homologyCoordinate_action_apply k I ((r ^ BinaryTensorTorus.binaryWeight I)⁻¹)
    (BinaryExteriorScaling.torusCoefficients k f r) n v a

/-- The actual degree-one fixed subspace has dimension at most one. -/
theorem finrank_fixed_one_le (r : kˣ) (hr : orderOf r = 2 ^ f - 1) (hf : 2 ≤ f) :
    Module.finrank k ((torusAction k I r 1).toLinearMap - LinearMap.id).ker ≤ 1 :=
  BinaryTorusFixedCoordinates.finrank_fixed_one_le k I r hr hf
    (torusAction k I r 1).toLinearMap (homologyCoordinate k I 0)
    (homologyCoordinate_injective k I 0) (homologyCoordinate_torusAction k I r 0)

/-- Every nonsingleton support has zero actual fixed degree-one homology. -/
theorem fixed_one_eq_bot (r : kˣ) (hr : orderOf r = 2 ^ f - 1) (hf : 2 ≤ f)
    (hI : I.card ≠ 1) :
    ((torusAction k I r 1).toLinearMap - LinearMap.id).ker = ⊥ :=
  BinaryTorusFixedCoordinates.fixed_one_eq_bot k I r hr hf hI
    (torusAction k I r 1).toLinearMap (homologyCoordinate k I 0)
    (homologyCoordinate_injective k I 0) (homologyCoordinate_torusAction k I r 0)

/-- Natural coefficients have at most one fixed degree-two class when f ≥ 3. -/
theorem finrank_fixed_two_le (r : kˣ) (hr : orderOf r = 2 ^ f - 1) (hf : 3 ≤ f)
    (i : Fin f) :
    Module.finrank k ((torusAction k {i} r 2).toLinearMap - LinearMap.id).ker ≤ 1 :=
  BinaryTorusFixedCoordinates.finrank_fixed_two_le k r hr hf i
    (torusAction k {i} r 2).toLinearMap (homologyCoordinate k {i} 1)
    (homologyCoordinate_injective k {i} 1) (homologyCoordinate_torusAction k {i} r 1)

/-- At f=2 the natural coefficients have zero fixed degree-two homology. -/
theorem fixed_two_at_two_eq_bot (r : kˣ) (hr : orderOf r = 2 ^ 2 - 1) (i : Fin 2) :
    ((torusAction k {i} r 2).toLinearMap - LinearMap.id).ker = ⊥ :=
  BinaryTorusFixedCoordinates.fixed_two_at_two_eq_bot k r hr i
    (torusAction k {i} r 2).toLinearMap (homologyCoordinate k {i} 1)
    (homologyCoordinate_injective k {i} 1) (homologyCoordinate_torusAction k {i} r 1)

end Kourovka2135.BinaryCochainTorusBounds
