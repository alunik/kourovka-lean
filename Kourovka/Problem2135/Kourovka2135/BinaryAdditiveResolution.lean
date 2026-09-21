import Kourovka2135.BinaryExteriorResolution
import Kourovka2135.BinaryExteriorGroupAlgebra
import Mathlib.RepresentationTheory.Rep.Iso
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic

/-! Transport of the explicit exterior-algebra resolution to the additive
finite field. The augmentation module is identified with the actual trivial
representation, so the resulting complex computes ordinary group cohomology. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Kourovka2135.BinaryAdditiveResolution
open CategoryTheory
open BinaryExteriorAlgebra BinaryExteriorAugmentation
open scoped IsMulCommutative ModuleCat.Algebra

variable (k : Type u) [Field k] [CharP k 2] (f : ℕ)
variable {F : Type u} [Field F] [Fintype F] (σ : F →+* k)
variable (hcard : Fintype.card F = 2 ^ f)

/-- The concrete multiplicative-tag group algebra equivalence. -/
def monoidEquivalence : MonoidAlgebra k (Multiplicative F) ≃ₐ[k] Carrier k f :=
  (AddMonoidAlgebra.toMultiplicativeAlgEquiv k k F).symm.trans
    (BinaryExteriorGroupAlgebra.equivalence k f σ hcard)

@[simp] theorem monoidEquivalence_single (g : Multiplicative F) (a : k) :
    monoidEquivalence k f σ hcard (MonoidAlgebra.single g a) =
      a • BinaryExteriorCharacter.character k f (σ g.toAdd) := by
  have h := AddMonoidAlgebra.toMultiplicativeAlgEquiv_single
    (R := k) (A := k) (M := F) g.toAdd a
  simp only [ofAdd_toAdd] at h
  rw [monoidEquivalence, AlgEquiv.trans_apply, ← h, AlgEquiv.symm_apply_apply]
  exact BinaryExteriorGroupAlgebra.equivalence_single k f σ hcard g.toAdd a

/-- The equivalence of module categories is followed by the standard
group-algebra/representation equivalence. -/
def representationEquivalence : ModuleCat.{u} (Carrier k f) ≌ Rep.{u} k (Multiplicative F) :=
  (ModuleCat.restrictScalarsEquivalenceOfRingEquiv
    (monoidEquivalence k f σ hcard).toRingEquiv).trans
    (Rep.equivalenceModuleMonoidAlgebra (k := k) (G := Multiplicative F)).symm

instance representationFunctorAdditive :
    (representationEquivalence k f σ hcard).functor.Additive where
  map_add := by
    intro M N p q
    apply Rep.hom_ext
    ext x
    rfl

/-- The transported residue object, before identifying its trivial action. -/
abbrev residueRepresentation : Rep.{u} k (Multiplicative F) :=
  (representationEquivalence k f σ hcard).functor.obj (BinaryExteriorResolution.residue k f)

/-- The underlying coefficient ring is unchanged, and scalar compatibility
follows from the two actual algebra homomorphisms. -/
def residueLinearEquiv : residueRepresentation k f σ hcard ≃ₗ[k] k where
  toFun := fun x => x
  invFun := fun x => x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r x := by
    change augmentation k f
      (monoidEquivalence k f σ hcard (algebraMap k (MonoidAlgebra k (Multiplicative F)) r)) *
        (show k from x) = r * (show k from x)
    rw [(monoidEquivalence k f σ hcard).commutes, (augmentation k f).commutes]
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- Every group element acts trivially because the character has augmentation one. -/
def residueIsoTrivial : residueRepresentation k f σ hcard ≅ Rep.trivial k (Multiplicative F) k :=
  Rep.mkIso (ρ := (residueRepresentation k f σ hcard).ρ)
    (σ := (Rep.trivial k (Multiplicative F) k).ρ) <| Representation.Equiv.mk
    (ρ := (residueRepresentation k f σ hcard).ρ)
    (σ := (Rep.trivial k (Multiplicative F) k).ρ)
    (residueLinearEquiv k f σ hcard) fun g => by
    apply LinearMap.ext
    intro x
    change augmentation k f
      (monoidEquivalence k f σ hcard (MonoidAlgebra.single g 1)) *
        (show k from x) = (show k from x)
    simp only [monoidEquivalence_single, one_smul, augmentation_character]
    exact one_mul (show k from x)

/-- Map the actual projective resolution along the proved categorical equivalence. -/
def transportedResolution : ProjectiveResolution (residueRepresentation k f σ hcard) :=
  (representationEquivalence k f σ hcard).functor.mapProjectiveResolution
    (BinaryExteriorResolution.projectiveResolution k f)

/-- The same explicit complex resolves the standard trivial representation. -/
def projectiveResolution : ProjectiveResolution (Rep.trivial k (Multiplicative F) k) where
  complex := (transportedResolution k f σ hcard).complex
  projective := (transportedResolution k f σ hcard).projective
  π := (transportedResolution k f σ hcard).π ≫
    (ChainComplex.single₀ _).map (residueIsoTrivial k f σ hcard).hom
  quasiIso := by infer_instance

/-- This explicit complex computes the usual group cohomology in every degree. -/
def groupCohomologyIso (V : Rep.{u} k (Multiplicative F)) (n : ℕ) :
    groupCohomology V n ≅
      ((projectiveResolution k f σ hcard).complex.linearYonedaObj k V).homology n :=
  _root_.groupCohomologyIso V n (projectiveResolution k f σ hcard)

end Kourovka2135.BinaryAdditiveResolution
