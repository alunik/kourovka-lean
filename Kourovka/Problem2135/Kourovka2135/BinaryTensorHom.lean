import Kourovka2135.BinaryExteriorHom
import Kourovka2135.BinaryTensorCoefficient
import Kourovka2135.CochainRaising
import Mathlib.LinearAlgebra.Finsupp.Defs

/-! The actual Hom differential in finite squarefree coefficient coordinates.

The degree index is finite, so functions on it are linearly equivalent to
finitely supported coefficient vectors. Under this equivalence the actual
Hom coboundary is precisely the graded raising differential. The proof uses
the concrete exterior-algebra action, with no coefficient-classification
or cohomology hypothesis.
-/

set_option autoImplicit false
noncomputable section
universe u

namespace Kourovka2135.BinaryTensorHom

open CategoryTheory PeriodicResolution
open scoped IsMulCommutative

section Evaluation

variable {ι B : Type*} [CommRing B]

/-- A raising column is pullback along the unique active lowering index,
followed by multiplication by the corresponding coefficient generator. -/
theorem gradedRaise_apply (x : ι → B) (i : ι) (n : ℕ)
    (v : DegreeSpace ι B n) (a : DegreeIndex ι (n + 1)) :
    CochainRaising.gradedRaise x i n v a =
      if hi : a.val i = 0 then 0 else v (lowerIndex i a hi) * x i := by
  classical
  induction v using Finsupp.induction_linear with
  | zero =>
      by_cases hi : a.val i = 0 <;> simp [hi]
  | add v w hv hw =>
      simp only [map_add, Finsupp.add_apply, hv, hw]
      split_ifs <;> simp [add_mul]
  | single b c =>
      rw [CochainRaising.gradedRaise_single]
      by_cases hi : a.val i = 0
      · have hne : raiseIndex i b ≠ a := by
          intro h
          have ha := raiseIndex_active i b
          rw [h, hi] at ha
          exact ha rfl
        simp [hi, hne]
      · have he : raiseIndex i b = a ↔ b = lowerIndex i a hi := by
          constructor
          · intro h
            exact (raiseIndex_injective i) (h.trans (raiseIndex_lowerIndex i a hi).symm)
          · intro h
            rw [h, raiseIndex_lowerIndex]
        simp [hi, Finsupp.single_apply, he, ite_mul]

/-- The coefficientwise formula for the finite sum of raising columns. -/
theorem gradedDifferential_apply (x : ι → B) (S : Finset ι) (n : ℕ)
    (v : DegreeSpace ι B n) (a : DegreeIndex ι (n + 1)) :
    CochainRaising.gradedDifferential x S n v a =
      ∑ i ∈ S, if hi : a.val i = 0 then 0 else v (lowerIndex i a hi) * x i := by
  simp only [CochainRaising.gradedDifferential, LinearMap.sum_apply,
    Finsupp.finsetSum_apply, gradedRaise_apply]

end Evaluation

variable (k : Type u) [CommRing k] {f : ℕ} (I : Finset (Fin f))

/-- The actual coefficient module over the full exterior algebra. -/
abbrev coefficientModule : ModuleCat.{u} (BinaryExteriorAlgebra.Carrier k f) :=
  ModuleCat.of _ (BinaryTensorCoefficient.Carrier k I)

/-- The images of the full algebra generators in the coefficient algebra. -/
def coefficientGenerator (i : Fin f) : BinaryTensorCoefficient.Carrier k I :=
  BinaryTensorCoefficient.projection k I (BinaryExteriorAlgebra.generator k f i)

theorem generator_smul_eq (i : Fin f) (v : BinaryTensorCoefficient.Carrier k I) :
    BinaryExteriorAlgebra.generator k f i • v = coefficientGenerator k I i * v := rfl

/-- A finite function cochain as a finitely supported graded coefficient vector. -/
def finiteCoordinates (n : ℕ) :
    (DegreeIndex (Fin f) n → BinaryTensorCoefficient.Carrier k I) ≃ₗ[k]
      DegreeSpace (Fin f) (BinaryTensorCoefficient.Carrier k I) n :=
  (Finsupp.linearEquivFunOnFinite k (BinaryTensorCoefficient.Carrier k I)
    (DegreeIndex (Fin f) n)).symm

@[simp] theorem finiteCoordinates_apply (n : ℕ)
    (c : DegreeIndex (Fin f) n → BinaryTensorCoefficient.Carrier k I)
    (a : DegreeIndex (Fin f) n) : finiteCoordinates k I n c a = c a := rfl

@[simp] theorem finiteCoordinates_symm_apply (n : ℕ)
    (v : DegreeSpace (Fin f) (BinaryTensorCoefficient.Carrier k I) n)
    (a : DegreeIndex (Fin f) n) : (finiteCoordinates k I n).symm v a = v a := rfl

variable [CharP k 2]

/-- Actual A-linear maps out of the free resolution, in finite coefficient coordinates. -/
def homCoordinates (n : ℕ) :
    (BinaryExteriorResolution.freeDegree k f n ⟶ coefficientModule k I) ≃ₗ[k]
      DegreeSpace (Fin f) (BinaryTensorCoefficient.Carrier k I) n :=
  (BinaryExteriorHom.homEquiv k f (coefficientModule k I) n).trans (finiteCoordinates k I n)

@[simp] theorem homCoordinates_apply (n : ℕ)
    (φ : BinaryExteriorResolution.freeDegree k f n ⟶ coefficientModule k I)
    (a : DegreeIndex (Fin f) n) :
    homCoordinates k I n φ a = φ.hom (Finsupp.single a 1) := rfl

/-- The actual coboundary becomes the graded raising map coefficient by coefficient. -/
theorem finiteCoordinates_coboundary (n : ℕ)
    (c : DegreeIndex (Fin f) n → BinaryTensorCoefficient.Carrier k I) :
    finiteCoordinates k I (n + 1)
        (BinaryExteriorHom.coboundary k f (coefficientModule k I) n c) =
      CochainRaising.gradedDifferential (coefficientGenerator k I) Finset.univ n
        (finiteCoordinates k I n c) := by
  apply Finsupp.ext
  intro a
  rw [finiteCoordinates_apply, BinaryExteriorHom.coboundary_apply,
    gradedDifferential_apply]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : a.val i = 0
  · simp [hi]
  · simp [hi, generator_smul_eq, mul_comm]

/-- Equality of the concrete ground-ring linear maps under finite-coordinate transport. -/
theorem coboundary_conjugation (n : ℕ) :
    (finiteCoordinates k I (n + 1)).toLinearMap.comp
        (BinaryExteriorHom.coboundary k f (coefficientModule k I) n) =
      ((CochainRaising.gradedDifferential (coefficientGenerator k I) Finset.univ n).restrictScalars k).comp
        (finiteCoordinates k I n).toLinearMap := by
  apply LinearMap.ext
  exact finiteCoordinates_coboundary k I n

/-- The equality starts with the Hom differential from the actual resolution. -/
theorem homCoordinates_homDifferential (n : ℕ)
    (φ : BinaryExteriorResolution.freeDegree k f n ⟶ coefficientModule k I) :
    homCoordinates k I (n + 1)
        (BinaryExteriorHom.homDifferential k f (coefficientModule k I) n φ) =
      CochainRaising.gradedDifferential (coefficientGenerator k I) Finset.univ n
        (homCoordinates k I n φ) := by
  simpa only [homCoordinates, LinearEquiv.trans_apply, BinaryExteriorHom.coboundary,
    LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] using
    finiteCoordinates_coboundary k I n
      (BinaryExteriorHom.homEquiv k f (coefficientModule k I) n φ)

/-- Explicitly, precomposing with the projective-resolution differential is raising. -/
theorem homCoordinates_precomp (n : ℕ)
    (φ : BinaryExteriorResolution.freeDegree k f n ⟶ coefficientModule k I) :
    homCoordinates k I (n + 1)
        ((BinaryExteriorResolution.projectiveResolution k f).complex.d (n + 1) n ≫ φ) =
      CochainRaising.gradedDifferential (coefficientGenerator k I) Finset.univ n
        (homCoordinates k I n φ) := by
  exact (congrArg (homCoordinates k I (n + 1))
    (BinaryExteriorHom.homDifferential_apply k f (coefficientModule k I) n φ)).symm.trans
      (homCoordinates_homDifferential k I n φ)

end Kourovka2135.BinaryTensorHom
