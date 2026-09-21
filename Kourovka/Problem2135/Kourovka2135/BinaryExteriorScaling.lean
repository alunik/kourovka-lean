import Kourovka2135.BinaryExteriorCharacter

/-! Diagonal algebra automorphisms of the binary exterior coordinate algebra.

The action is induced by an actual invertible linear map on the generators.
In characteristic two, each squarefree basis vector has the corresponding
product weight. The binary torus weights intertwine the additive character
with multiplication of its parameter by the square of the torus parameter.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.BinaryExteriorScaling

open Kourovka2135.BinaryExteriorAlgebra
open Kourovka2135.BinaryExteriorCharacter

variable (k : Type*) [CommRing k] (f : ℕ)

/-- Coordinatewise multiplication by units on the space of generators. -/
def diagonal (c : Fin f → kˣ) : (Fin f → k) ≃ₗ[k] (Fin f → k) where
  toFun v i := (c i : k) * v i
  invFun v i := (((c i)⁻¹ : kˣ) : k) * v i
  left_inv v := by
    funext i
    simp [← mul_assoc]
  right_inv v := by
    funext i
    simp [← mul_assoc]
  map_add' v w := by
    funext i
    simp only [Pi.add_apply, mul_add]
  map_smul' a v := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

@[simp] theorem diagonal_apply (c : Fin f → kˣ) (v : Fin f → k) (i : Fin f) :
    diagonal k f c v i = (c i : k) * v i := rfl

theorem diagonal_basis (c : Fin f → kˣ) (i : Fin f) :
    diagonal k f c (Pi.basisFun k (Fin f) i) =
      (c i : k) • Pi.basisFun k (Fin f) i := by
  ext j
  by_cases h : i = j
  · subst j
    simp [Pi.basisFun_apply]
  · simp [Pi.basisFun_apply, Ne.symm h]

/-- The algebra automorphism induced by coordinatewise unit scaling. -/
def scale (c : Fin f → kˣ) : Carrier k f ≃ₐ[k] Carrier k f :=
  AlgEquiv.ofAlgHom
    (ExteriorAlgebra.map (diagonal k f c).toLinearMap)
    (ExteriorAlgebra.map (diagonal k f c).symm.toLinearMap)
    (by
      apply ExteriorAlgebra.hom_ext
      apply LinearMap.ext
      intro v
      change ExteriorAlgebra.map (diagonal k f c).toLinearMap
        (ExteriorAlgebra.map (diagonal k f c).symm.toLinearMap
          (ExteriorAlgebra.ι k v)) = ExteriorAlgebra.ι k v
      rw [ExteriorAlgebra.map_apply_ι, ExteriorAlgebra.map_apply_ι]
      exact congrArg (ExteriorAlgebra.ι k) ((diagonal k f c).apply_symm_apply v))
    (by
      apply ExteriorAlgebra.hom_ext
      apply LinearMap.ext
      intro v
      change ExteriorAlgebra.map (diagonal k f c).symm.toLinearMap
        (ExteriorAlgebra.map (diagonal k f c).toLinearMap
          (ExteriorAlgebra.ι k v)) = ExteriorAlgebra.ι k v
      rw [ExteriorAlgebra.map_apply_ι, ExteriorAlgebra.map_apply_ι]
      exact congrArg (ExteriorAlgebra.ι k) ((diagonal k f c).symm_apply_apply v))

@[simp] theorem scale_apply_ι (c : Fin f → kˣ) (v : Fin f → k) :
    scale k f c (ExteriorAlgebra.ι k v) =
      ExteriorAlgebra.ι k (diagonal k f c v) :=
  ExteriorAlgebra.map_apply_ι _ _

@[simp] theorem scale_generator (c : Fin f → kˣ) (i : Fin f) :
    scale k f c (generator k f i) = (c i : k) • generator k f i := by
  rw [generator, scale_apply_ι, diagonal_basis, map_smul]

@[simp] theorem scale_one :
    scale k f (1 : Fin f → kˣ) = 1 := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply ExteriorAlgebra.hom_ext
  apply LinearMap.ext
  intro v
  change scale k f 1 (ExteriorAlgebra.ι k v) = ExteriorAlgebra.ι k v
  rw [scale_apply_ι]
  congr 1
  ext i
  simp

/-- Multiplication of the parameters is composition of the actual automorphisms. -/
theorem scale_mul (c d : Fin f → kˣ) :
    scale k f (c * d) = scale k f c * scale k f d := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply ExteriorAlgebra.hom_ext
  apply LinearMap.ext
  intro v
  change scale k f (c * d) (ExteriorAlgebra.ι k v) =
    scale k f c (scale k f d (ExteriorAlgebra.ι k v))
  rw [scale_apply_ι, scale_apply_ι, scale_apply_ι]
  congr 1
  ext i
  simp [mul_assoc]

/-- The complete diagonal torus acts by algebra automorphisms. -/
def scaleHom : (Fin f → kˣ) →* (Carrier k f ≃ₐ[k] Carrier k f) where
  toFun := scale k f
  map_one' := scale_one k f
  map_mul' := scale_mul k f

@[simp] theorem scaleHom_apply (c : Fin f → kˣ) :
    scaleHom k f c = scale k f c := rfl

/-- Binary weights for the split torus parameter. -/
def torusCoefficients (r : kˣ) (i : Fin f) : kˣ := r ^ (2 ^ (i.val + 1))

/-- The torus automorphism with weight `2^(i+1)` on generator `i`. -/
def torusScale (r : kˣ) : Carrier k f ≃ₐ[k] Carrier k f :=
  scale k f (torusCoefficients k f r)

@[simp] theorem torusScale_generator (r : kˣ) (i : Fin f) :
    torusScale k f r (generator k f i) =
      (r : k) ^ (2 ^ (i.val + 1)) • generator k f i := by
  simp [torusScale, torusCoefficients]

@[simp] theorem torusScale_one : torusScale k f 1 = 1 := by
  have h : torusCoefficients k f 1 = 1 := by
    ext i
    simp [torusCoefficients]
  rw [torusScale, h, scale_one]

theorem torusScale_mul (r s : kˣ) :
    torusScale k f (r * s) = torusScale k f r * torusScale k f s := by
  have h : torusCoefficients k f (r * s) =
      torusCoefficients k f r * torusCoefficients k f s := by
    ext i
    simp [torusCoefficients, mul_pow]
  simp only [torusScale, h, scale_mul]

/-- The one-parameter torus action as a homomorphism. -/
def torusScaleHom : kˣ →* (Carrier k f ≃ₐ[k] Carrier k f) where
  toFun := torusScale k f
  map_one' := torusScale_one k f
  map_mul' := torusScale_mul k f

@[simp] theorem torusScaleHom_apply (r : kˣ) :
    torusScaleHom k f r = torusScale k f r := rfl

variable [CharP k 2]
open scoped CharTwo IsMulCommutative

/-- Every squarefree monomial scales by the product of its generator weights. -/
theorem scale_basis (c : Fin f → kˣ) (J : Finset (Fin f)) :
    scale k f c (basis k f J) =
      (∏ i ∈ J, (c i : k)) • basis k f J := by
  have hb : basis k f J = ∏ i ∈ J, generator k f i := by
    simpa using (prod_smul_generator k f J (fun _ => (1 : k))).symm
  conv_lhs => rw [hb]
  rw [map_prod]
  simp only [scale_generator]
  exact prod_smul_generator k f J (fun i => (c i : k))

/-- The explicit binary exponent of a squarefree torus weight. -/
theorem torusScale_basis (r : kˣ) (J : Finset (Fin f)) :
    torusScale k f r (basis k f J) =
      (r : k) ^ (∑ i ∈ J, 2 ^ (i.val + 1)) • basis k f J := by
  rw [torusScale, scale_basis]
  simp only [torusCoefficients, Units.val_pow_eq_pow_val, Finset.prod_pow_eq_pow_sum]

/-- The torus action intertwines the actual character with its squared parameter action. -/
theorem torusScale_character (r : kˣ) (t : k) :
    torusScale k f r (character k f t) =
      character k f ((r : k) ^ 2 * t) := by
  simp only [character, map_prod, map_add, map_one, map_smul,
    torusScale_generator, smul_smul]
  apply Finset.prod_congr rfl
  intro i _
  have hp : 2 ^ (i.val + 1) = 2 * 2 ^ i.val := by
    rw [pow_succ, Nat.mul_comm]
  rw [hp, pow_mul, mul_pow]
  congr 2
  ring

end Kourovka2135.BinaryExteriorScaling
