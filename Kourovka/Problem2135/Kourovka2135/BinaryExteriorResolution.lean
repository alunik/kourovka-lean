import Kourovka2135.PeriodicResolutionCoordinates
import Kourovka2135.PeriodicResolutionGraded
import Kourovka2135.BinaryExteriorAugmentation
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Abelian.Projective.Resolution

/-! The actual free resolution of the augmentation module of the binary
exterior algebra. Exactness is deduced from the conserved-weight contraction
and homogeneous projection; it is not an input to the construction.

The categorical augmentation/quasi-isomorphism packaging follows the
Apache-2.0 Tau Ceti dual-number resolution already vendored in
`Vendor/TauCeti/Algebra/Homology/Ext/DualNumbers.lean`.
-/
set_option autoImplicit false
noncomputable section
universe u
namespace Kourovka2135.BinaryExteriorResolution
open CategoryTheory CategoryTheory.Abelian
open BinaryExteriorAlgebra BinaryExteriorAugmentation PeriodicResolution
open scoped IsMulCommutative ModuleCat.Algebra

variable (k : Type u) [CommRing k] [CharP k 2] (f : ℕ)

instance carrierCharP : CharP (Carrier k f) 2 :=
  charP_of_injective_algebraMap
    (ExteriorAlgebra.algebraMap_leftInverse (Fin f → k)).injective 2

/-- Degree n of the actual free complex, as a module-category object. -/
abbrev freeDegree (n : ℕ) : ModuleCat.{u} (Carrier k f) :=
  ModuleCat.of _ (DegreeSpace (Fin f) (Carrier k f) n)

/-- The actual augmentation module: the ground ring acted on through augmentation. -/
abbrev residue : ModuleCat.{u} (Carrier k f) :=
  (ModuleCat.restrictScalars (augmentation k f).toRingHom).obj (ModuleCat.of k k)

/-- Evaluation in the unique degree-zero index followed by the residue map. -/
def augmentationMap : freeDegree k f 0 ⟶ residue k f :=
  ModuleCat.ofHom (X := freeDegree k f 0) (Y := residue k f)
    { toFun := fun v => augmentation k f (v default)
      map_add' := fun v w => by
        change augmentation k f (v default + w default) = _
        exact map_add (augmentation k f) _ _
      map_smul' := fun a v => by
        change augmentation k f (a * v default) =
          augmentation k f a * augmentation k f (v default)
        exact map_mul (augmentation k f) _ _ }

@[simp] theorem augmentationMap_apply (v : freeDegree k f 0) :
    (augmentationMap k f).hom v = augmentation k f (v default) := rfl

@[simp] theorem augmentationMap_single (a : DegreeIndex (Fin f) 0) (c : Carrier k f) :
    (augmentationMap k f).hom (Finsupp.single a c) = augmentation k f c := by
  have ha : a = default := Subsingleton.elim _ _
  subst a
  change augmentation k f ((Finsupp.single default c) default) = augmentation k f c
  rw [Finsupp.single_eq_same]

theorem augmentationMap_surjective : Function.Surjective (augmentationMap k f).hom := by
  intro x
  obtain ⟨a, ha⟩ := augmentation_surjective k f x
  refine ⟨Finsupp.single default a, ?_⟩
  exact (augmentationMap_single k f default a).trans ha

/-- Degree-zero embedding preserves the unique coefficient. -/
theorem embedDegree_zero_apply (v : DegreeSpace (Fin f) (Carrier k f) 0) :
    embedDegree 0 v 0 = v default :=
  Finsupp.mapDomain_apply (degreeIndexEmbedding 0).injective v default

/-- Positive homogeneous degrees have no exponent-zero coefficient. -/
theorem embedDegree_succ_apply_zero (n : ℕ)
    (v : DegreeSpace (Fin f) (Carrier k f) (n + 1)) : embedDegree (n + 1) v 0 = 0 := by
  apply Finsupp.mapDomain_of_notMem_range
  rintro ⟨a, ha⟩
  change a.val = 0 at ha
  have hd := a.property
  rw [ha] at hd
  simp at hd

/-- The ungraded differential kills the entire degree-zero module. -/
theorem differential_embedDegree_zero (v : DegreeSpace (Fin f) (Carrier k f) 0) :
    differential (generator k f) Finset.univ (embedDegree 0 v) = 0 := by
  suffices h : (differential (generator k f) Finset.univ).comp (embedDegree 0) = 0 from
    LinearMap.congr_fun h v
  apply Finsupp.lhom_ext
  intro a c
  have ha : a.val = 0 := (Finsupp.degree_eq_zero_iff a.val).mp a.property
  simp [LinearMap.comp_apply, differential, ha]

/-- Actual exactness in every positive homological degree. -/
theorem range_gradedDifferential_eq_ker (n : ℕ) :
    (gradedDifferential (generator k f) Finset.univ (n + 1)).range =
      (gradedDifferential (generator k f) Finset.univ n).ker := by
  ext v
  constructor
  · rintro ⟨w, rfl⟩
    exact LinearMap.congr_fun
      (gradedDifferential_comp (generator k f) Finset.univ
        (fun i _ => generator_square k f i) n) w
  · intro hv
    change gradedDifferential (generator k f) Finset.univ n v = 0 at hv
    apply exists_graded_preimage_of_ungraded_preimage (generator k f) Finset.univ (n + 1) v
    apply exists_boundary_of_cycle_of_zero_coordinate k f (embedDegree (n + 1) v)
    · rw [← embedDegree_gradedDifferential_apply, hv, map_zero]
    · simp [embedDegree_succ_apply_zero]

/-- The residue map kills the degree-one differential. -/
theorem augmentationMap_comp_gradedDifferential :
    (augmentationMap k f).hom.comp
      (gradedDifferential (generator k f) Finset.univ 0) = 0 := by
  apply Finsupp.lhom_ext
  intro a c
  simp only [LinearMap.comp_apply, gradedDifferential, LinearMap.sum_apply,
    map_sum, LinearMap.zero_apply]
  apply Finset.sum_eq_zero
  intro i _
  rw [gradedLower_single]
  split_ifs
  · exact map_zero _
  · rw [augmentationMap_single, map_mul, augmentation_generator, mul_zero]
    rfl

/-- Exactness at degree zero is the actual augmentation-kernel identity. -/
theorem range_gradedDifferential_eq_ker_augmentationMap :
    (gradedDifferential (generator k f) Finset.univ 0).range =
      (augmentationMap k f).hom.ker := by
  ext v
  constructor
  · rintro ⟨w, rfl⟩
    exact LinearMap.congr_fun (augmentationMap_comp_gradedDifferential k f) w
  · intro hv
    change augmentation k f (v default) = 0 at hv
    apply exists_graded_preimage_of_ungraded_preimage (generator k f) Finset.univ 0 v
    apply exists_boundary_of_cycle_of_zero_coordinate k f (embedDegree 0 v)
    · exact differential_embedDegree_zero k f v
    · rw [embedDegree_zero_apply, ← augmentation_eq_repr_empty]
      exact hv

/-- The genuine chain complex on the free degree modules. -/
def complex : ChainComplex (ModuleCat.{u} (Carrier k f)) ℕ :=
  ChainComplex.of (freeDegree k f)
    (fun n => ModuleCat.ofHom (gradedDifferential (generator k f) Finset.univ n))
    (fun n => ModuleCat.hom_ext
      (gradedDifferential_comp (generator k f) Finset.univ
        (fun i _ => generator_square k f i) n))

@[simp] theorem complex_d (n : ℕ) :
    (complex k f).d (n + 1) n =
      ModuleCat.ofHom (gradedDifferential (generator k f) Finset.univ n) := by
  simp [complex]

/-- The actual augmentation chain map. -/
def complexπ : complex k f ⟶ (ChainComplex.single₀ (ModuleCat.{u} (Carrier k f))).obj
    (residue k f) :=
  ((complex k f).toSingle₀Equiv (residue k f)).symm
    ⟨augmentationMap k f, by
      rw [complex_d]
      exact ModuleCat.hom_ext (augmentationMap_comp_gradedDifferential k f)⟩

@[simp] theorem complexπ_f_zero : (complexπ k f).f 0 = augmentationMap k f :=
  ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

/-- The augmentation module has this explicit free projective resolution.
All exactness obligations are discharged from the actual block contraction. -/
def projectiveResolution : ProjectiveResolution (residue k f) where
  complex := complex k f
  projective n := ModuleCat.projective_of_free (degreeBasis (ι := Fin f) (A := Carrier k f) n)
  π := complexπ k f
  quasiIso := by
    constructor
    intro m
    induction m with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros' _ rfl rfl rfl]
      refine ⟨?_, ?_⟩
      · rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
        simpa [complex_d, complexπ_f_zero] using!
          range_gradedDifferential_eq_ker_augmentationMap k f
      · rw [ModuleCat.epi_iff_surjective]
        exact augmentationMap_surjective k f
    | succ m _ =>
      rw [quasiIsoAt_iff_exactAt' (hL := ChainComplex.exactAt_succ_single_obj ..),
        HomologicalComplex.exactAt_iff' _ (m + 2) (m + 1) m (by simp) (by simp),
        ShortComplex.moduleCat_exact_iff_range_eq_ker]
      simpa [complex_d] using! range_gradedDifferential_eq_ker k f m

/-- Each term is identified with its actual degree-indexed free module. -/
def projectiveResolutionXIso (n : ℕ) :
    (projectiveResolution k f).complex.X n ≅ freeDegree k f n := Iso.refl _

@[simp] theorem projectiveResolution_d (n : ℕ) :
    (projectiveResolution k f).complex.d (n + 1) n =
      ModuleCat.ofHom (gradedDifferential (generator k f) Finset.univ n) :=
  complex_d k f n

@[simp] theorem projectiveResolution_π_f_zero :
    (projectiveResolution k f).π.f 0 = augmentationMap k f := complexπ_f_zero k f

end Kourovka2135.BinaryExteriorResolution
