import Kourovka2135.BinaryCochainGraded
import Kourovka2135.BinaryTensorHom
import Mathlib.CategoryTheory.Abelian.Ext

/-! The actual coefficient cochain complex and its comparison with Hom of
the explicit projective resolution. This is an isomorphism of complexes,
not merely a dimension comparison or a chosen differential formula. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Kourovka2135.BinaryCochainComplex
open CategoryTheory BinaryCochainGraded
open scoped IsMulCommutative ModuleCat.Algebra
variable (k : Type u) [CommRing k] [CharP k 2] {f : ℕ} (I : Finset (Fin f))

def complex : CochainComplex (ModuleCat.{u} k) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of k (DegreeCochains k I n))
    (fun n => ModuleCat.ofHom (differential k I n))
    (fun n => ModuleCat.hom_ext (differential_comp k I n))

@[simp] theorem complex_d (n : ℕ) :
    (complex k I).d n (n + 1) = ModuleCat.ofHom (differential k I n) := by
  simp [complex]

/-- The categorical Hom module uses scalar restriction through the algebra.
This agrees with the native coefficient scalars by their actual scalar tower. -/
def complexCoordinates (n : ℕ) :
    ((BinaryExteriorResolution.projectiveResolution k f).complex.linearYonedaObj k
      (BinaryTensorHom.coefficientModule k I)).X n ≃ₗ[k] DegreeCochains k I n where
  toFun := BinaryTensorHom.homCoordinates k I n
  invFun := (BinaryTensorHom.homCoordinates k I n).symm
  left_inv := (BinaryTensorHom.homCoordinates k I n).left_inv
  right_inv := (BinaryTensorHom.homCoordinates k I n).right_inv
  map_add' := (BinaryTensorHom.homCoordinates k I n).map_add
  map_smul' r φ := by
    apply Finsupp.ext
    intro a
    change (algebraMap k (BinaryExteriorAlgebra.Carrier k f) r) •
        φ.hom (Finsupp.single a 1) = r • φ.hom (Finsupp.single a 1)
    exact IsScalarTower.algebraMap_smul _ _ _

/-- The actual Hom complex is isomorphic to the graded raising complex. -/
def homComplexIso :
    (BinaryExteriorResolution.projectiveResolution k f).complex.linearYonedaObj k
      (BinaryTensorHom.coefficientModule k I) ≅ complex k I :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (complexCoordinates k I n).toModuleIso)
    (by
      intro n m hnm
      change n + 1 = m at hnm
      subst m
      rw [complex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro φ
      exact (BinaryTensorHom.homCoordinates_precomp k I n φ).symm)

/-- The complex comparison induces the corresponding homology comparison. -/
def homologyIso (n : ℕ) :
    ((BinaryExteriorResolution.projectiveResolution k f).complex.linearYonedaObj k
      (BinaryTensorHom.coefficientModule k I)).homology n ≅ (complex k I).homology n :=
  (HomologicalComplex.homologyFunctor (ModuleCat k) (ComplexShape.up ℕ) n).mapIso
    (homComplexIso k I)

end Kourovka2135.BinaryCochainComplex
