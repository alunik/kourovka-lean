import Kourovka2135.BinaryTensorSubsetBasis
import Kourovka2135.BinaryExteriorScaling
import Mathlib.LinearAlgebra.Basis.SMul

/-! Actual diagonal and torus actions on the binary coefficient modules.

All diagonal weights are units, so the maps are genuine linear equivalences.
The coefficient action intertwines the algebra automorphism that scales its
generators. The one-parameter torus weights are written as quotients of
natural powers of a unit, avoiding truncated natural-number subtraction.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.BinaryTensorTorus

open BinaryTensorSubsetBasis
open scoped IsMulCommutative

variable (k : Type*) [CommRing k] {f : ℕ} (I : Finset (Fin f))

/-- A common scalar and the product of the included generator weights. -/
def weight (ell : kˣ) (c : Fin f → kˣ) (J : Subsets I) : kˣ :=
  ell * ∏ i ∈ J.val, c i

theorem weight_insert (ell : kˣ) (c : Fin f → kˣ) (i : Fin f) (hi : i ∈ I)
    (J : Subsets I) (hij : i ∉ J.val) :
    weight k I ell c (insertIndex I i hi J) = c i * weight k I ell c J := by
  simp only [weight, insertIndex_val, Finset.prod_insert hij]
  exact mul_left_comm _ _ _

/-- An invertible diagonal operator on the actual coefficient basis. -/
def diagonal (ell : kˣ) (c : Fin f → kˣ) :
    BinaryTensorCoefficient.Carrier k I ≃ₗ[k] BinaryTensorCoefficient.Carrier k I :=
  (basis k I).equiv ((basis k I).unitsSMul (weight k I ell c)) (Equiv.refl _)

@[simp] theorem diagonal_basis (ell : kˣ) (c : Fin f → kˣ) (J : Subsets I) :
    diagonal k I ell c (basis k I J) = (weight k I ell c J : k) • basis k I J := by
  simp only [diagonal, Module.Basis.equiv_apply, Equiv.refl_apply,
    Module.Basis.unitsSMul_apply, Units.smul_def]

@[simp] theorem diagonal_one : diagonal k I 1 1 = 1 := by
  apply (basis k I).ext'
  intro J
  change diagonal k I 1 1 (basis k I J) = basis k I J
  rw [diagonal_basis]
  simp [weight]

theorem diagonal_mul (ell mu : kˣ) (c d : Fin f → kˣ) :
    diagonal k I (ell * mu) (c * d) = diagonal k I ell c * diagonal k I mu d := by
  apply (basis k I).ext'
  intro J
  change diagonal k I (ell * mu) (c * d) (basis k I J) =
    diagonal k I ell c (diagonal k I mu d (basis k I J))
  rw [diagonal_basis, diagonal_basis, map_smul, diagonal_basis, smul_smul]
  congr 1
  simp [weight, Finset.prod_mul_distrib, mul_assoc, mul_left_comm, mul_comm]

/-- Ordinary natural binary weights, prior to passage to a torus character. -/
def binaryWeight (J : Finset (Fin f)) : ℕ := ∑ i ∈ J, 2 ^ i.val

theorem torus_weight (r : kˣ) (J : Subsets I) :
    weight k I ((r ^ binaryWeight I)⁻¹) (BinaryExteriorScaling.torusCoefficients k f r) J =
      r ^ (2 * binaryWeight J.val) / r ^ binaryWeight I := by
  have hs : (∑ i ∈ J.val, 2 ^ (i.val + 1)) = 2 * binaryWeight J.val := by
    unfold binaryWeight
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [pow_succ, Nat.mul_comm]
  simp only [weight, BinaryExteriorScaling.torusCoefficients,
    Finset.prod_pow_eq_pow_sum, hs, div_eq_mul_inv]
  exact mul_comm _ _

/-- The actual split-torus action on the coefficient module. -/
def torus (r : kˣ) :
    BinaryTensorCoefficient.Carrier k I ≃ₗ[k] BinaryTensorCoefficient.Carrier k I :=
  diagonal k I ((r ^ binaryWeight I)⁻¹) (BinaryExteriorScaling.torusCoefficients k f r)

/-- The basis vector indexed by J has weight `2 weight(J) - weight(I)`,
expressed without natural-number subtraction. -/
@[simp] theorem torus_basis (r : kˣ) (J : Subsets I) :
    torus k I r (basis k I J) =
      ((r ^ (2 * binaryWeight J.val) / r ^ binaryWeight I : kˣ) : k) • basis k I J := by
  rw [torus, diagonal_basis, torus_weight]

@[simp] theorem torus_one : torus k I 1 = 1 := by
  have hc : BinaryExteriorScaling.torusCoefficients k f (1 : kˣ) = 1 := by
    ext i
    simp [BinaryExteriorScaling.torusCoefficients]
  simp only [torus, one_pow, inv_one, hc, diagonal_one]

theorem torus_mul (r s : kˣ) : torus k I (r * s) = torus k I r * torus k I s := by
  have hc : BinaryExteriorScaling.torusCoefficients k f (r * s) =
      BinaryExteriorScaling.torusCoefficients k f r *
        BinaryExteriorScaling.torusCoefficients k f s := by
    ext i
    simp [BinaryExteriorScaling.torusCoefficients, mul_pow]
  have hell : ((r * s) ^ binaryWeight I)⁻¹ =
      (r ^ binaryWeight I)⁻¹ * (s ^ binaryWeight I)⁻¹ := by
    simp [mul_pow, mul_comm]
  rw [torus, hell, hc, diagonal_mul]
  rfl

/-- The torus acts through genuine linear automorphisms. -/
def torusHom : kˣ →* (BinaryTensorCoefficient.Carrier k I ≃ₗ[k]
    BinaryTensorCoefficient.Carrier k I) where
  toFun := torus k I
  map_one' := torus_one k I
  map_mul' := torus_mul k I

@[simp] theorem torusHom_apply (r : kˣ) : torusHom k I r = torus k I r := rfl

variable [CharP k 2]

/-- Actual generator intertwining for the diagonal coefficient operator. -/
theorem diagonal_generator (ell : kˣ) (c : Fin f → kˣ) (i : Fin f)
    (v : BinaryTensorCoefficient.Carrier k I) :
    diagonal k I ell c (BinaryExteriorAlgebra.generator k f i • v) =
      (c i : k) • (BinaryExteriorAlgebra.generator k f i • diagonal k I ell c v) := by
  have he : (diagonal k I ell c).toLinearMap.comp
      (LinearMap.mulLeft k
        (BinaryTensorCoefficient.projection k I (BinaryExteriorAlgebra.generator k f i))) =
      (c i : k) • ((LinearMap.mulLeft k
        (BinaryTensorCoefficient.projection k I (BinaryExteriorAlgebra.generator k f i))).comp
          (diagonal k I ell c).toLinearMap) := by
    apply (basis k I).ext
    intro J
    change diagonal k I ell c (BinaryExteriorAlgebra.generator k f i • basis k I J) =
      (c i : k) • (BinaryExteriorAlgebra.generator k f i • diagonal k I ell c (basis k I J))
    rw [diagonal_basis]
    rw [← smul_comm (weight k I ell c J : k) (BinaryExteriorAlgebra.generator k f i) (basis k I J)]
    simp only [generator_smul_basis]
    split_ifs with h
    · rw [diagonal_basis, weight_insert k I ell c i h.1 J h.2]
      simp only [Units.val_mul, smul_smul]
    · simp
  exact LinearMap.congr_fun he v

private theorem diagonal_monomial_smul (ell : kˣ) (c : Fin f → kˣ)
    (J : Finset (Fin f)) (v : BinaryTensorCoefficient.Carrier k I) :
    diagonal k I ell c (BinaryExteriorAlgebra.basis k f J • v) =
      BinaryExteriorScaling.scale k f c (BinaryExteriorAlgebra.basis k f J) •
        diagonal k I ell c v := by
  induction J using Finset.induction_on generalizing v with
  | empty => simp
  | @insert i J hi ih =>
      have hb : BinaryExteriorAlgebra.basis k f (insert i J) =
          BinaryExteriorAlgebra.generator k f i * BinaryExteriorAlgebra.basis k f J := by
        simpa [hi] using (BinaryExteriorAlgebra.generator_mul_basis k f i J).symm
      rw [hb, map_mul]
      simp only [mul_smul, BinaryExteriorScaling.scale_generator,
        diagonal_generator, ih, smul_assoc]

/-- Compatibility with the complete actual algebra scaling action. -/
theorem diagonal_smul (ell : kˣ) (c : Fin f → kˣ)
    (a : BinaryExteriorAlgebra.Carrier k f) (v : BinaryTensorCoefficient.Carrier k I) :
    diagonal k I ell c (a • v) =
      BinaryExteriorScaling.scale k f c a • diagonal k I ell c v := by
  have he : (diagonal k I ell c).toLinearMap.comp
      ((LinearMap.mulRight k v).comp (BinaryTensorCoefficient.projection k I).toLinearMap) =
      (LinearMap.mulRight k (diagonal k I ell c v)).comp
        ((BinaryTensorCoefficient.projection k I).toLinearMap.comp
          (BinaryExteriorScaling.scale k f c).toLinearMap) := by
    apply (BinaryExteriorAlgebra.basis k f).ext
    intro J
    exact diagonal_monomial_smul k I ell c J v
  exact LinearMap.congr_fun he a

/-- The torus coefficient action intertwines the algebra's torus automorphism. -/
theorem torus_smul (r : kˣ) (a : BinaryExteriorAlgebra.Carrier k f)
    (v : BinaryTensorCoefficient.Carrier k I) :
    torus k I r (a • v) = BinaryExteriorScaling.torusScale k f r a • torus k I r v :=
  diagonal_smul k I ((r ^ binaryWeight I)⁻¹)
    (BinaryExteriorScaling.torusCoefficients k f r) a v

theorem torus_generator (r : kˣ) (i : Fin f) (v : BinaryTensorCoefficient.Carrier k I) :
    torus k I r (BinaryExteriorAlgebra.generator k f i • v) =
      (r : k) ^ (2 ^ (i.val + 1)) •
        (BinaryExteriorAlgebra.generator k f i • torus k I r v) := by
  simpa only [torus, BinaryExteriorScaling.torusCoefficients, Units.val_pow_eq_pow_val] using
    diagonal_generator k I ((r ^ binaryWeight I)⁻¹)
      (BinaryExteriorScaling.torusCoefficients k f r) i v

/-- Compatibility with the actual additive character and squared torus parameter action. -/
theorem torus_character_smul (r : kˣ) (t : k) (v : BinaryTensorCoefficient.Carrier k I) :
    torus k I r (BinaryExteriorCharacter.character k f t • v) =
      BinaryExteriorCharacter.character k f ((r : k) ^ 2 * t) • torus k I r v := by
  rw [torus_smul, BinaryExteriorScaling.torusScale_character]

end Kourovka2135.BinaryTensorTorus
