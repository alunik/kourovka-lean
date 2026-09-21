import Kourovka2135.BinaryCochainTorus
import Kourovka2135.BinarySurvivorWeights
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.FieldTheory.Finite.Basic

/-! Exact unit-valued torus characters on conserved cochain blocks.
The character is one precisely at the previously proved modular-weight
indices. No finite-field generator or cohomology equivariance is assumed
here: this lemma applies to any unit with the specified actual order. -/
set_option autoImplicit false
noncomputable section
namespace Kourovka2135.BinaryTorusCharacterWeights
open BinarySurvivorWeights BinaryTensorTorus
variable (k : Type*) [CommRing k] {f : ℕ} (I : Finset (Fin f))

/-- The exponent-vector weight specializes to a single power of the torus parameter. -/
theorem exponentWeight_torus (r : kˣ) (a : Fin f →₀ ℕ) :
    BinaryCochainTorus.exponentWeight k (BinaryExteriorScaling.torusCoefficients k f r) a =
      r ^ generatorWeight a := by
  simp only [BinaryCochainTorus.exponentWeight, BinaryExteriorScaling.torusCoefficients,
    ← pow_mul, Finset.prod_pow_eq_pow_sum]
  congr 1
  simp only [generatorWeight, Finsupp.weight_eq_sum, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  exact Nat.mul_comm _ _

/-- The coefficient twist cancels half the top monomial weight, leaving the
signed weight `weight(I)-generatorWeight(w)` as an exact quotient of units. -/
theorem blockWeight_torus (r : kˣ) (w : Fin f →₀ ℕ) :
    BinaryCochainTorus.blockWeight k I ((r ^ binaryWeight I)⁻¹)
      (BinaryExteriorScaling.torusCoefficients k f r) w =
      r ^ binaryWeight I / r ^ generatorWeight w := by
  change BinaryTensorTorus.weight k I ((r ^ binaryWeight I)⁻¹)
      (BinaryExteriorScaling.torusCoefficients k f r) (BinaryTensorSubsetBasis.topIndex I) /
        BinaryCochainTorus.exponentWeight k (BinaryExteriorScaling.torusCoefficients k f r) w = _
  rw [torus_weight, exponentWeight_torus]
  change (r ^ (2 * binaryWeight I) / r ^ binaryWeight I) / r ^ generatorWeight w = _
  rw [two_mul, pow_add]
  simp

/-- Triviality of the actual unit character is exactly equality of powers modulo its order. -/
theorem blockWeight_torus_eq_one_iff (r : kˣ) (w : Fin f →₀ ℕ) :
    BinaryCochainTorus.blockWeight k I ((r ^ binaryWeight I)⁻¹)
      (BinaryExteriorScaling.torusCoefficients k f r) w = 1 ↔
      Nat.ModEq (orderOf r) (binaryWeight I) (generatorWeight w) := by
  rw [blockWeight_torus, div_eq_one]
  exact RightCancelMonoid.pow_eq_pow_iff_modEq

/-- The scalar action has weight one at exactly the same indices as the unit character. -/
theorem scalar_blockWeight_eq_one_iff (r : kˣ) (w : Fin f →₀ ℕ)
    (hr : orderOf r = 2 ^ f - 1) :
    ((BinaryCochainTorus.blockWeight k I ((r ^ binaryWeight I)⁻¹)
      (BinaryExteriorScaling.torusCoefficients k f r) w : kˣ) : k) = 1 ↔
      Nat.ModEq (2 ^ f - 1) (∑ i ∈ I, 2 ^ i.val) (generatorWeight w) := by
  have hu : ∀ z : kˣ, (z : k) = 1 ↔ z = 1 := fun z =>
    ⟨fun h => Units.ext h, fun h => by rw [h]; rfl⟩
  rw [hu, blockWeight_torus_eq_one_iff, hr]
  rfl

/-- A finite parameter field supplies a unit of exactly the required order,
and its image in the coefficient field retains that order. -/
theorem exists_primitive_image {K F : Type*} [Field K] [Field F] [Fintype F]
    (σ : F →+* K) (hcard : Fintype.card F = 2 ^ f) :
    ∃ r : Fˣ, orderOf (Units.map σ.toMonoidHom r) = 2 ^ f - 1 := by
  classical
  obtain ⟨r, hr⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Fˣ)
  refine ⟨r, ?_⟩
  rw [orderOf_injective (Units.map σ.toMonoidHom) (Units.map_injective σ.injective),
    hr, Nat.card_eq_fintype_card, Fintype.card_units, hcard]

end Kourovka2135.BinaryTorusCharacterWeights
