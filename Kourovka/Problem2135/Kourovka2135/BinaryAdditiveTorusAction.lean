import Kourovka2135.BinaryAdditiveCohomology
import Kourovka2135.BinaryTensorTorus
import Kourovka2135.ResolutionConjugation

/-! The actual coefficient morphism for inverse torus conjugation on the
additive parameter group. Its underlying linear map is the forward torus
action, and equivariance is proved from the actual additive character.
-/
set_option autoImplicit false
noncomputable section
universe u
namespace Kourovka2135.BinaryAdditiveTorusAction
open CategoryTheory BinaryAdditiveCohomology
open scoped IsMulCommutative ModuleCat.Algebra

/-- Squared-parameter multiplication as an automorphism of the additive group. -/
def parameter {F : Type*} [Field F] (r : Fˣ) : Multiplicative F ≃* Multiplicative F where
  toFun g := Multiplicative.ofAdd ((r : F) ^ 2 * g.toAdd)
  invFun g := Multiplicative.ofAdd (((r⁻¹ : Fˣ) : F) ^ 2 * g.toAdd)
  left_inv g := by simp
  right_inv g := by simp
  map_mul' g h := by simp [mul_add]

@[simp] theorem parameter_toAdd {F : Type*} [Field F] (r : Fˣ) (g : Multiplicative F) :
    (parameter r g).toAdd = (r : F) ^ 2 * g.toAdd := rfl

@[simp] theorem parameter_symm {F : Type*} [Field F] (r : Fˣ) :
    (parameter r).symm = parameter r⁻¹ := by
  apply MulEquiv.ext
  intro g
  rfl

/-- Bundle a pointwise restriction-intertwining equation without unfolding the coefficient model. -/
def restrictionMorphism {K G : Type*} [CommRing K] [Group G]
    (A : Rep K G) (s : G →* G) (T : Module.End K A)
    (hT : ∀ g v, T (A.ρ (s g) v) = A.ρ g (T v)) : Rep.res s A ⟶ A :=
  Rep.ofHom { toLinearMap := T, isIntertwining' := fun g => LinearMap.ext (hT g) }

@[simp] theorem restrictionMorphism_apply {K G : Type*} [CommRing K] [Group G]
    (A : Rep K G) (s : G →* G) (T : Module.End K A)
    (hT : ∀ g v, T (A.ρ (s g) v) = A.ρ g (T v)) (v : A) :
    (restrictionMorphism A s T hT).hom v = T v := rfl

variable (k : Type u) [Field k] [CharP k 2] {f : ℕ} (I : Finset (Fin f))
variable {F : Type u} [Field F] [Fintype F] (σ : F →+* k)
variable (hcard : Fintype.card F = 2 ^ f)

/-- The actual forward torus action on the transported coefficient vector space. -/
def coefficientLinear (r : Fˣ) :
    coefficientRepresentation k I σ hcard ≃ₗ[k] coefficientRepresentation k I σ hcard :=
  (coefficientLinearEquiv k I σ hcard).trans
    ((BinaryTensorTorus.torus k I (Units.map σ.toMonoidHom r)).trans
      (coefficientLinearEquiv k I σ hcard).symm)

@[simp] theorem coefficientLinear_apply (r : Fˣ)
    (v : coefficientRepresentation k I σ hcard) :
    coefficientLinearEquiv k I σ hcard (coefficientLinear k I σ hcard r v) =
      BinaryTensorTorus.torus k I (Units.map σ.toMonoidHom r)
        (coefficientLinearEquiv k I σ hcard v) := by
  simp [coefficientLinear]

/-- Forward coefficient action intertwines the inverse-conjugated group action. -/
theorem coefficientLinear_intertwines (r : Fˣ) (g : Multiplicative F)
    (v : coefficientRepresentation k I σ hcard) :
    coefficientLinear k I σ hcard r
        ((coefficientRepresentation k I σ hcard).ρ (parameter r⁻¹ g) v) =
      (coefficientRepresentation k I σ hcard).ρ g
        (coefficientLinear k I σ hcard r v) := by
  apply (coefficientLinearEquiv k I σ hcard).injective
  rw [coefficientLinear_apply, coefficient_action, coefficient_action,
    coefficientLinear_apply]
  change BinaryTensorTorus.torus k I (Units.map σ.toMonoidHom r)
      (BinaryExteriorCharacter.character k f (σ (parameter r⁻¹ g).toAdd) •
        coefficientLinearEquiv k I σ hcard v) =
    BinaryExteriorCharacter.character k f (σ g.toAdd) •
      BinaryTensorTorus.torus k I (Units.map σ.toMonoidHom r)
        (coefficientLinearEquiv k I σ hcard v)
  rw [BinaryTensorTorus.torus_character_smul]
  congr 2
  simp only [parameter_toAdd, map_mul, map_pow, Units.coe_map]
  rw [← mul_assoc, ← mul_pow]
  change (σ (r : F) * σ ((r⁻¹ : Fˣ) : F)) ^ 2 * σ g.toAdd = σ g.toAdd
  rw [← σ.map_mul]
  simp

/-- The coefficient morphism used by ordinary group-cohomology functoriality. -/
def coefficientMap (r : Fˣ) :
    Rep.res (parameter r⁻¹).toMonoidHom (coefficientRepresentation k I σ hcard) ⟶
      coefficientRepresentation k I σ hcard :=
  restrictionMorphism (coefficientRepresentation k I σ hcard)
    (parameter r⁻¹).toMonoidHom (coefficientLinear k I σ hcard r).toLinearMap
    (coefficientLinear_intertwines k I σ hcard r)

/-- The actual map on ordinary group cohomology for inverse conjugation and
forward coefficient action. -/
def cohomologyMap (r : Fˣ) (n : ℕ) :
    groupCohomology (coefficientRepresentation k I σ hcard) n ⟶
      groupCohomology (coefficientRepresentation k I σ hcard) n :=
  groupCohomology.map (parameter r⁻¹).toMonoidHom (coefficientMap k I σ hcard r) n

/-- Coordinates on the entire Hom complex of the transported resolution. -/
def homComplexIso :
    (BinaryAdditiveResolution.projectiveResolution k f σ hcard).complex.linearYonedaObj k
        (coefficientRepresentation k I σ hcard) ≅ BinaryCochainComplex.complex k I :=
  (LinearFunctorHomComplex.complexIso k
    (BinaryAdditiveResolution.representationEquivalence k f σ hcard).functor
    (BinaryExteriorResolution.projectiveResolution k f).complex
    (BinaryTensorHom.coefficientModule k I)).symm ≪≫ BinaryCochainComplex.homComplexIso k I

/-- Direct bar-resolution comparison, followed by the actual monomial coordinates. -/
def groupCohomologyIso (n : ℕ) :
    groupCohomology (coefficientRepresentation k I σ hcard) n ≅
      (BinaryCochainComplex.complex k I).homology n :=
  ResolutionConjugation.groupCohomologyIso (coefficientRepresentation k I σ hcard)
      (BinaryAdditiveResolution.projectiveResolution k f σ hcard) n ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat k) (ComplexShape.up ℕ) n).mapIso
      (homComplexIso k I σ hcard)

end Kourovka2135.BinaryAdditiveTorusAction
