import Kourovka2135.BinaryResolutionScaling
import Kourovka2135.BinaryCochainTorusEvaluation
import Kourovka2135.BinaryCochainTorusComplex

/-! The semilinear resolution action is the concrete diagonal on Hom
coordinates. Together with direct bar comparison this identifies the actual
ordinary group-cohomology action, without assuming equivariance.
-/
set_option autoImplicit false
noncomputable section
universe u
namespace Kourovka2135.BinaryAdditiveTorusCoordinates
open CategoryTheory PeriodicResolution BinaryAdditiveCohomology
open BinaryAdditiveTorusAction BinaryResolutionScaling
open scoped IsMulCommutative ModuleCat.Algebra
variable (k : Type u) [Field k] [CharP k 2] {f : ℕ} (I : Finset (Fin f))
variable {F : Type u} [Field F] [Fintype F] (σ : F →+* k)
variable (hcard : Fintype.card F = 2 ^ f)

/-- Evaluation coordinates of the actual transported Hom complex. -/
def homCoordinates (n : ℕ) :
    ((BinaryAdditiveResolution.projectiveResolution k f σ hcard).complex.X n ⟶
      coefficientRepresentation k I σ hcard) →ₗ[k] BinaryCochainGraded.DegreeCochains k I n :=
  ((homComplexIso k I σ hcard).hom.f n).hom

/-- The categorical comparison really evaluates at the free resolution generators. -/
theorem homCoordinates_apply (n : ℕ)
    (φ : (BinaryAdditiveResolution.projectiveResolution k f σ hcard).complex.X n ⟶
      coefficientRepresentation k I σ hcard) (a : DegreeIndex (Fin f) n) :
    homCoordinates k I σ hcard n φ a =
      coefficientLinearEquiv k I σ hcard (φ.hom (Finsupp.single a 1)) := by
  let E := (BinaryAdditiveResolution.representationEquivalence k f σ hcard).functor
  obtain ⟨ψ, rfl⟩ := (LinearFunctorHomComplex.homEquiv k E
    ((BinaryExteriorResolution.projectiveResolution k f).complex.X n)
    (BinaryTensorHom.coefficientModule k I)).surjective φ
  change BinaryCochainComplex.complexCoordinates k I n
    ((LinearFunctorHomComplex.homEquiv k E _ _).symm
      (LinearFunctorHomComplex.homEquiv k E _ _ ψ)) a = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

/-- The actual endomorphism of the resolution's Hom complex. -/
def homAction (r : Fˣ) :
    (BinaryAdditiveResolution.projectiveResolution k f σ hcard).complex.linearYonedaObj k
        (coefficientRepresentation k I σ hcard) ⟶
      (BinaryAdditiveResolution.projectiveResolution k f σ hcard).complex.linearYonedaObj k
        (coefficientRepresentation k I σ hcard) :=
  ResolutionConjugation.semilinearHom k (Rep.resFunctor (parameter r⁻¹).toMonoidHom)
    (BinaryAdditiveResolution.projectiveResolution k f σ hcard).complex
    (coefficientRepresentation k I σ hcard) (torusChainMap k f σ hcard r⁻¹)
    (coefficientMap k I σ hcard r)

set_option backward.isDefEq.respectTransparency false in
/-- Evaluation exposes the inverse resolution weight and forward coefficient action. -/
theorem homCoordinates_action (r : Fˣ) (n : ℕ)
    (φ : (BinaryAdditiveResolution.projectiveResolution k f σ hcard).complex.X n ⟶
      coefficientRepresentation k I σ hcard) (a : DegreeIndex (Fin f) n) :
    homCoordinates k I σ hcard n ((homAction k I σ hcard r).f n φ) a =
      (BinaryResolutionScaling.exponentWeight k f
        (BinaryExteriorScaling.torusCoefficients k f (Units.map σ.toMonoidHom r⁻¹))
          a.val : k) •
        BinaryTensorTorus.torus k I (Units.map σ.toMonoidHom r)
          (homCoordinates k I σ hcard n φ a) := by
  change homCoordinates k I σ hcard n
    (torusComponent k f σ hcard r⁻¹ n ≫
      (Rep.resFunctor (parameter r⁻¹).toMonoidHom).map φ ≫
      coefficientMap k I σ hcard r) a = _
  rw [homCoordinates_apply]
  change coefficientLinearEquiv k I σ hcard
    ((coefficientMap k I σ hcard r).hom
      (((Rep.resFunctor (parameter r⁻¹).toMonoidHom).map φ).hom
        ((torusComponent k f σ hcard r⁻¹ n).hom (Finsupp.single a 1)))) = _
  rw [torusComponent_single_one]
  let x : Rep.res (parameter r⁻¹).toMonoidHom
      ((BinaryAdditiveResolution.projectiveResolution k f σ hcard).complex.X n) :=
    Finsupp.single a 1
  change coefficientLinearEquiv k I σ hcard
    ((coefficientMap k I σ hcard r).hom
      (((Rep.resFunctor (parameter r⁻¹).toMonoidHom).map φ).hom
        ((BinaryResolutionScaling.exponentWeight k f
          (BinaryExteriorScaling.torusCoefficients k f (Units.map σ.toMonoidHom r⁻¹))
            a.val : k) • x))) = _
  rw [map_smul, map_smul, map_smul]
  congr 1
  change coefficientLinearEquiv k I σ hcard
    ((restrictionMorphism (coefficientRepresentation k I σ hcard)
      (parameter r⁻¹).toMonoidHom (coefficientLinear k I σ hcard r).toLinearMap
      (coefficientLinear_intertwines k I σ hcard r)).hom
      (φ.hom (Finsupp.single a 1))) = _
  rw [restrictionMorphism_apply]
  exact (coefficientLinear_apply k I σ hcard r (φ.hom (Finsupp.single a 1))).trans
    (congrArg (BinaryTensorTorus.torus k I (Units.map σ.toMonoidHom r))
      (homCoordinates_apply k I σ hcard n φ a).symm)

omit [CharP k 2] [Fintype F] in
/-- Inverse parameter scaling contributes the inverse cochain exponent weight. -/
theorem inverse_exponentWeight (r : Fˣ) (a : Fin f →₀ ℕ) :
    BinaryResolutionScaling.exponentWeight k f
        (BinaryExteriorScaling.torusCoefficients k f (Units.map σ.toMonoidHom r⁻¹)) a =
      (BinaryCochainTorus.exponentWeight k
        (BinaryExteriorScaling.torusCoefficients k f (Units.map σ.toMonoidHom r)) a)⁻¹ := by
  simp [BinaryResolutionScaling.exponentWeight, BinaryCochainTorus.exponentWeight,
    BinaryExteriorScaling.torusCoefficients, ← Finset.prod_inv_distrib]

/-- The actual semilinear Hom action becomes the concrete graded diagonal. -/
theorem homCoordinates_action_eq_diagonal (r : Fˣ) (n : ℕ)
    (φ : (BinaryAdditiveResolution.projectiveResolution k f σ hcard).complex.X n ⟶
      coefficientRepresentation k I σ hcard) :
    homCoordinates k I σ hcard n ((homAction k I σ hcard r).f n φ) =
      BinaryCochainTorusGraded.diagonal k I
        (((Units.map σ.toMonoidHom r) ^ BinaryTensorTorus.binaryWeight I)⁻¹)
        (BinaryExteriorScaling.torusCoefficients k f (Units.map σ.toMonoidHom r)) n
        (homCoordinates k I σ hcard n φ) := by
  apply Finsupp.ext
  intro a
  rw [homCoordinates_action, inverse_exponentWeight,
    BinaryCochainTorusEvaluation.diagonal_apply_value]
  rfl

/-- The concrete cochain torus automorphism with the parameter embedded in k. -/
def cochainTorusIso (r : Fˣ) :
    BinaryCochainComplex.complex k I ≅ BinaryCochainComplex.complex k I :=
  BinaryCochainTorusComplex.diagonalIso k I
    (((Units.map σ.toMonoidHom r) ^ BinaryTensorTorus.binaryWeight I)⁻¹)
    (BinaryExteriorScaling.torusCoefficients k f (Units.map σ.toMonoidHom r))

/-- The actual Hom-complex comparison intertwines the two concrete actions. -/
theorem homComplexIso_naturality (r : Fˣ) :
    homAction k I σ hcard r ≫ (homComplexIso k I σ hcard).hom =
      (homComplexIso k I σ hcard).hom ≫ (cochainTorusIso k I σ r).hom := by
  ext n φ
  change homCoordinates k I σ hcard n ((homAction k I σ hcard r).f n φ) =
    (BinaryCochainTorusGraded.diagonalEquiv k I
      (((Units.map σ.toMonoidHom r) ^ BinaryTensorTorus.binaryWeight I)⁻¹)
      (BinaryExteriorScaling.torusCoefficients k f (Units.map σ.toMonoidHom r)) n).toLinearMap
        (homCoordinates k I σ hcard n φ)
  rw [BinaryCochainTorusGraded.diagonalEquiv_toLinearMap]
  exact homCoordinates_action_eq_diagonal k I σ hcard r n φ

/-- Ordinary group-cohomology functoriality is the concrete diagonal action
under the direct bar-resolution comparison. -/
theorem groupCohomologyIso_naturality (r : Fˣ) (n : ℕ) :
    (BinaryAdditiveTorusAction.groupCohomologyIso k I σ hcard n).hom ≫
        HomologicalComplex.homologyMap (cochainTorusIso k I σ r).hom n =
      cohomologyMap k I σ hcard r n ≫
        (BinaryAdditiveTorusAction.groupCohomologyIso k I σ hcard n).hom := by
  have hbar := ResolutionConjugation.groupCohomologyIso_naturality (parameter r⁻¹)
    (coefficientRepresentation k I σ hcard)
    (BinaryAdditiveResolution.projectiveResolution k f σ hcard)
    (torusChainMap k f σ hcard r⁻¹) (torusChainMap_π k f σ hcard r⁻¹)
    (coefficientMap k I σ hcard r) n
  have hcoord := congrArg (fun p => HomologicalComplex.homologyMap p n)
    (homComplexIso_naturality k I σ hcard r)
  simp only [HomologicalComplex.homologyMap_comp] at hcoord
  change (ResolutionConjugation.groupCohomologyIso
      (coefficientRepresentation k I σ hcard)
      (BinaryAdditiveResolution.projectiveResolution k f σ hcard) n).hom ≫
    HomologicalComplex.homologyMap (homAction k I σ hcard r) n =
      cohomologyMap k I σ hcard r n ≫
        (ResolutionConjugation.groupCohomologyIso
          (coefficientRepresentation k I σ hcard)
          (BinaryAdditiveResolution.projectiveResolution k f σ hcard) n).hom at hbar
  change ((ResolutionConjugation.groupCohomologyIso
      (coefficientRepresentation k I σ hcard)
      (BinaryAdditiveResolution.projectiveResolution k f σ hcard) n).hom ≫
        HomologicalComplex.homologyMap (homComplexIso k I σ hcard).hom n) ≫ _ =
      _ ≫ ((ResolutionConjugation.groupCohomologyIso
        (coefficientRepresentation k I σ hcard)
        (BinaryAdditiveResolution.projectiveResolution k f σ hcard) n).hom ≫
          HomologicalComplex.homologyMap (homComplexIso k I σ hcard).hom n)
  rw [Category.assoc, ← hcoord, ← Category.assoc, hbar, Category.assoc]

end Kourovka2135.BinaryAdditiveTorusCoordinates
