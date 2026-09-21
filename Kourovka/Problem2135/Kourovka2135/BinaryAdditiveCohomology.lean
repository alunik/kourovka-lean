import Kourovka2135.BinaryAdditiveResolution
import Kourovka2135.BinaryCochainComplex
import Kourovka2135.LinearFunctorHomComplex

/-! The ordinary group cohomology of the actual squarefree coefficient
representation is computed by the explicit raising complex. Both changes
of category are actual linear isomorphisms of Hom complexes. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Kourovka2135.BinaryAdditiveCohomology
open CategoryTheory BinaryAdditiveResolution
open scoped IsMulCommutative ModuleCat.Algebra
variable (k : Type u) [Field k] [CharP k 2] {f : ℕ} (I : Finset (Fin f))
variable {F : Type u} [Field F] [Fintype F] (σ : F →+* k)
variable (hcard : Fintype.card F = 2 ^ f)

/-- The categorical equivalence respects the ground-field scalar action. -/
instance representationFunctorLinear :
    (representationEquivalence k f σ hcard).functor.Linear k where
  map_smul := by
    intro M N φ r
    apply Rep.hom_ext
    ext x
    change (algebraMap k (BinaryExteriorAlgebra.Carrier k f) r) • φ.hom x =
      (monoidEquivalence k f σ hcard (algebraMap k (MonoidAlgebra k (Multiplicative F)) r)) • φ.hom x
    rw [(monoidEquivalence k f σ hcard).commutes]

/-- The actual additive-group coefficient representation, transported from its algebra module. -/
def coefficientRepresentation : Rep.{u} k (Multiplicative F) :=
  (representationEquivalence k f σ hcard).functor.obj (BinaryTensorHom.coefficientModule k I)

/-- Its underlying vector space is the concrete coefficient exterior algebra. -/
def coefficientLinearEquiv :
    coefficientRepresentation k I σ hcard ≃ₗ[k] BinaryTensorCoefficient.Carrier k I where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r x := by
    change BinaryTensorCoefficient.projection k I
      (monoidEquivalence k f σ hcard (algebraMap k (MonoidAlgebra k (Multiplicative F)) r)) *
        (show BinaryTensorCoefficient.Carrier k I from x) =
      r • (show BinaryTensorCoefficient.Carrier k I from x)
    rw [(monoidEquivalence k f σ hcard).commutes,
      (BinaryTensorCoefficient.projection k I).commutes, Algebra.smul_def]

/-- The action is multiplication by the explicit additive character projected
to the included coefficient generators. -/
theorem coefficient_action (g : Multiplicative F)
    (v : coefficientRepresentation k I σ hcard) :
    coefficientLinearEquiv k I σ hcard ((coefficientRepresentation k I σ hcard).ρ g v) =
      BinaryTensorCoefficient.projection k I
        (BinaryExteriorCharacter.character k f (σ g.toAdd)) *
          coefficientLinearEquiv k I σ hcard v := by
  change BinaryTensorCoefficient.projection k I
    (monoidEquivalence k f σ hcard (MonoidAlgebra.single g 1)) *
      (show BinaryTensorCoefficient.Carrier k I from v) = _
  simp only [monoidEquivalence_single, one_smul]
  rfl

/-- Every ordinary group-cohomology degree is the homology of the actual
explicit coefficient complex. -/
def groupCohomologyIso (n : ℕ) :
    groupCohomology (coefficientRepresentation k I σ hcard) n ≅
      (BinaryCochainComplex.complex k I).homology n :=
  BinaryAdditiveResolution.groupCohomologyIso k f σ hcard
      (coefficientRepresentation k I σ hcard) n ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat k) (ComplexShape.up ℕ) n).mapIso
      (LinearFunctorHomComplex.complexIso k
        (representationEquivalence k f σ hcard).functor
        (BinaryExteriorResolution.projectiveResolution k f).complex
        (BinaryTensorHom.coefficientModule k I)).symm ≪≫
    BinaryCochainComplex.homologyIso k I n

end Kourovka2135.BinaryAdditiveCohomology
