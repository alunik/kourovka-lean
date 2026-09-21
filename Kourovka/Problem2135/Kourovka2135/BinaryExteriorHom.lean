import Kourovka2135.BinaryExteriorResolution
import Mathlib.Algebra.Category.ModuleCat.Algebra

/-! Actual Hom coordinates and cochain differential for arbitrary compatible
coefficient modules over the binary exterior algebra. Evaluation on the free
basis is a ground-ring linear equivalence. The differential has no exponent
multiplicity and no coefficient-classification hypothesis.
-/
set_option autoImplicit false
noncomputable section
universe u
namespace Kourovka2135.BinaryExteriorHom
open CategoryTheory
open BinaryExteriorAlgebra BinaryExteriorResolution PeriodicResolution
open scoped IsMulCommutative

variable (k : Type u) [CommRing k] [CharP k 2] (f : ℕ)
variable (M : ModuleCat.{u} (Carrier k f)) [Module k M] [IsScalarTower k (Carrier k f) M]

/-- A-linear maps out of the actual degree module are their values on its
single-coefficient basis; the equivalence is linear over the ground ring. -/
def homEquiv (n : ℕ) :
    (freeDegree k f n ⟶ M) ≃ₗ[k] (DegreeIndex (Fin f) n → M) :=
  (ModuleCat.homLinearEquiv (S := k)).trans
    ((degreeBasis (ι := Fin f) (A := Carrier k f) n).constr k).symm

@[simp] theorem homEquiv_apply (n : ℕ) (φ : freeDegree k f n ⟶ M)
    (a : DegreeIndex (Fin f) n) :
    homEquiv k f M n φ a = φ.hom (Finsupp.single a 1) := rfl

/-- The inverse is exactly the A-linear extension by finite linear combination. -/
theorem homEquiv_symm_hom (n : ℕ) (c : DegreeIndex (Fin f) n → M) :
    ((homEquiv k f M n).symm c).hom = Finsupp.linearCombination (Carrier k f) c := by
  change (degreeBasis (ι := Fin f) (A := Carrier k f) n).constr k c = _
  apply (degreeBasis (ι := Fin f) (A := Carrier k f) n).ext
  intro a
  rw [Module.Basis.constr_basis]
  change c a = Finsupp.linearCombination (Carrier k f) c (Finsupp.single a 1)
  simp

/-- Precomposition by the actual adjacent differential, as a k-linear map. -/
def homDifferential (n : ℕ) :
    (freeDegree k f n ⟶ M) →ₗ[k] (freeDegree k f (n + 1) ⟶ M) where
  toFun φ := ModuleCat.ofHom
    (φ.hom.comp (gradedDifferential (generator k f) Finset.univ n))
  map_add' _ _ := ModuleCat.hom_ext rfl
  map_smul' _ _ := ModuleCat.hom_ext rfl

@[simp] theorem homDifferential_apply (n : ℕ) (φ : freeDegree k f n ⟶ M) :
    homDifferential k f M n φ = (projectiveResolution k f).complex.d (n + 1) n ≫ φ := by
  rw [projectiveResolution_d]
  rfl

/-- The actual Hom differential expressed in the free-basis coordinates. -/
def coboundary (n : ℕ) :
    (DegreeIndex (Fin f) n → M) →ₗ[k] (DegreeIndex (Fin f) (n + 1) → M) :=
  (homEquiv k f M (n + 1)).toLinearMap.comp
    ((homDifferential k f M n).comp (homEquiv k f M n).symm.toLinearMap)

/-- Each active exponent contributes exactly one generator action, with no
factor equal to that exponent. -/
theorem coboundary_apply (n : ℕ) (c : DegreeIndex (Fin f) n → M)
    (a : DegreeIndex (Fin f) (n + 1)) :
    coboundary k f M n c a = ∑ i : Fin f,
      if hi : a.val i = 0 then 0 else generator k f i • c (lowerIndex i a hi) := by
  change ((homEquiv k f M n).symm c).hom
    (gradedDifferential (generator k f) Finset.univ n (Finsupp.single a 1)) = _
  rw [homEquiv_symm_hom]
  simp only [gradedDifferential, LinearMap.sum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : a.val i = 0 <;> simp [hi]

/-- The coordinate formula is induced by precomposition with the actual
projective-resolution differential, not a separately specified complex. -/
theorem homEquiv_precomp_apply (n : ℕ) (φ : freeDegree k f n ⟶ M)
    (a : DegreeIndex (Fin f) (n + 1)) :
    homEquiv k f M (n + 1) ((projectiveResolution k f).complex.d (n + 1) n ≫ φ) a =
      ∑ i : Fin f, if hi : a.val i = 0 then 0 else
        generator k f i • homEquiv k f M n φ (lowerIndex i a hi) := by
  rw [projectiveResolution_d, homEquiv_apply]
  change φ.hom
    (gradedDifferential (generator k f) Finset.univ n (Finsupp.single a 1)) = _
  simp only [gradedDifferential, LinearMap.sum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : a.val i = 0
  · simp [hi]
  · simpa [hi, Finsupp.smul_single] using
      φ.hom.map_smul (generator k f i) (Finsupp.single (lowerIndex i a hi) 1)

/-- Precomposition gives consecutive Hom differentials with composite zero. -/
theorem homDifferential_comp (n : ℕ) :
    (homDifferential k f M (n + 1)).comp (homDifferential k f M n) = 0 := by
  apply LinearMap.ext
  intro φ
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro v
  change φ.hom (gradedDifferential (generator k f) Finset.univ n
    (gradedDifferential (generator k f) Finset.univ (n + 1) v)) = 0
  have hz := LinearMap.congr_fun
    (gradedDifferential_comp (generator k f) Finset.univ
      (fun i _ => generator_square k f i) n) v
  change gradedDifferential (generator k f) Finset.univ n
    (gradedDifferential (generator k f) Finset.univ (n + 1) v) = 0 at hz
  rw [hz, map_zero]

/-- The coordinate coboundaries consequently compose to zero. -/
theorem coboundary_comp (n : ℕ) :
    (coboundary k f M (n + 1)).comp (coboundary k f M n) = 0 := by
  apply LinearMap.ext
  intro c
  change homEquiv k f M (n + 2)
    (homDifferential k f M (n + 1)
      ((homEquiv k f M (n + 1)).symm
        (homEquiv k f M (n + 1)
          (homDifferential k f M n ((homEquiv k f M n).symm c))))) = 0
  rw [LinearEquiv.symm_apply_apply]
  have hz := LinearMap.congr_fun (homDifferential_comp k f M n) ((homEquiv k f M n).symm c)
  change homDifferential k f M (n + 1)
    (homDifferential k f M n ((homEquiv k f M n).symm c)) = 0 at hz
  rw [hz, map_zero]

end Kourovka2135.BinaryExteriorHom
