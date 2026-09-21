import Kourovka2135.ResolutionDegree
import Kourovka2135.PeriodicResolutionOperators
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.RingTheory.Finiteness.Finsupp

/-! The actual degree modules and differentials of the tensor-periodic
construction. Each degree embeds in the ungraded free module, and the
intertwining identity transfers square-zero to consecutive degree maps.
This constructs a differential; it makes no exactness assertion.
-/
set_option autoImplicit false
noncomputable section
namespace Kourovka2135.PeriodicResolution

variable {ι : Type*}
variable {A : Type*} [CommRing A]

/-- The free A-module on exponent vectors of total degree n. -/
abbrev DegreeSpace (ι : Type*) (A : Type*) [Zero A] (n : ℕ) :=
  DegreeIndex ι n →₀ A

instance degreeSpaceFree (n : ℕ) : Module.Free A (DegreeSpace ι A n) :=
  inferInstance

instance degreeSpaceFinite [Finite ι] (n : ℕ) : Module.Finite A (DegreeSpace ι A n) :=
  inferInstance

/-- The standard basis consists of degree-indexed single coefficients. -/
def degreeBasis (n : ℕ) : Module.Basis (DegreeIndex ι n) A (DegreeSpace ι A n) :=
  Finsupp.basisSingleOne

/-- Insert one homogeneous degree into the ungraded exponent-indexed module. -/
def embedDegree (n : ℕ) : DegreeSpace ι A n →ₗ[A] Space ι A :=
  Finsupp.lmapDomain A A (degreeIndexEmbedding n)

theorem embedDegree_injective (n : ℕ) :
    Function.Injective (embedDegree (ι := ι) (A := A) n) :=
  Finsupp.mapDomain_injective (degreeIndexEmbedding n).injective

@[simp] theorem embedDegree_single (n : ℕ) (a : DegreeIndex ι n) (c : A) :
    embedDegree n (Finsupp.single a c) = Finsupp.single a.val c := by
  simp [embedDegree]

/-- Extract a homogeneous degree by restricting coefficient indices. -/
def projectDegree (n : ℕ) : Space ι A →ₗ[A] DegreeSpace ι A n :=
  Finsupp.lcomapDomain (R := A) (M := A) (degreeIndexEmbedding n)
    (degreeIndexEmbedding n).injective

@[simp] theorem projectDegree_embedDegree (n : ℕ) :
    (projectDegree (ι := ι) (A := A) n).comp (embedDegree n) = LinearMap.id := by
  apply LinearMap.ext
  intro v
  exact Finsupp.leftInverse_lcomapDomain_mapDomain (R := A) (M := A)
    (degreeIndexEmbedding n) (degreeIndexEmbedding n).injective v

@[simp] theorem projectDegree_embedDegree_apply (n : ℕ) (v : DegreeSpace ι A n) :
    projectDegree n (embedDegree n v) = v :=
  LinearMap.congr_fun (projectDegree_embedDegree n) v

/-- Projection retains exactly those basis vectors in the specified degree. -/
theorem projectDegree_single (n : ℕ) (a : ι →₀ ℕ) (c : A) :
    projectDegree n (Finsupp.single a c) =
      if ha : a.degree = n then Finsupp.single (⟨a, ha⟩ : DegreeIndex ι n) c else 0 := by
  classical
  by_cases ha : a.degree = n
  · rw [dite_eq_left ha]
    exact Finsupp.comapDomain_single (degreeIndexEmbedding n) ⟨a, ha⟩ c _
  · rw [dite_eq_right ha]
    have hnot : a ∉ Set.range (degreeIndexEmbedding n) := by
      rintro ⟨b, hb⟩
      apply ha
      change b.val = a at hb
      rw [← hb]
      exact b.property
    exact Finsupp.comapDomain_single_of_not_mem_range hnot c _

/-- The i-th graded column lowers an active exponent exactly once and
multiplies its coefficient by x i; there is no exponent multiplicity. -/
def gradedLower (x : ι → A) (i : ι) (n : ℕ) :
    DegreeSpace ι A (n + 1) →ₗ[A] DegreeSpace ι A n :=
  Finsupp.linearCombination A fun a =>
    if hi : a.val i = 0 then 0 else Finsupp.single (lowerIndex i a hi) (x i)

@[simp] theorem gradedLower_single (x : ι → A) (i : ι) (n : ℕ)
    (a : DegreeIndex ι (n + 1)) (c : A) :
    gradedLower x i n (Finsupp.single a c) =
      if hi : a.val i = 0 then 0 else Finsupp.single (lowerIndex i a hi) (c * x i) := by
  by_cases hi : a.val i = 0 <;>
    simp [gradedLower, hi, Finsupp.smul_single, smul_eq_mul]

/-- Graded lowering is the restriction of the actual ungraded lowering operator. -/
theorem embedDegree_gradedLower (x : ι → A) (i : ι) (n : ℕ) :
    (embedDegree n).comp (gradedLower x i n) =
      (lower x i).comp (embedDegree (n + 1)) := by
  apply Finsupp.lhom_ext
  intro a c
  by_cases hi : a.val i = 0 <;> simp [LinearMap.comp_apply, hi]

@[simp] theorem embedDegree_gradedLower_apply (x : ι → A) (i : ι) (n : ℕ)
    (v : DegreeSpace ι A (n + 1)) :
    embedDegree n (gradedLower x i n v) = lower x i (embedDegree (n + 1) v) :=
  LinearMap.congr_fun (embedDegree_gradedLower x i n) v

/-- The actual degree-n differential from degree n+1. -/
def gradedDifferential (x : ι → A) (S : Finset ι) (n : ℕ) :
    DegreeSpace ι A (n + 1) →ₗ[A] DegreeSpace ι A n :=
  ∑ i ∈ S, gradedLower x i n

/-- The homogeneous differential intertwines with the ungraded differential. -/
theorem embedDegree_gradedDifferential (x : ι → A) (S : Finset ι) (n : ℕ) :
    (embedDegree n).comp (gradedDifferential x S n) =
      (differential x S).comp (embedDegree (n + 1)) := by
  apply LinearMap.ext
  intro v
  simp only [LinearMap.comp_apply, gradedDifferential, differential,
    LinearMap.sum_apply, map_sum, embedDegree_gradedLower_apply]

@[simp] theorem embedDegree_gradedDifferential_apply
    (x : ι → A) (S : Finset ι) (n : ℕ) (v : DegreeSpace ι A (n + 1)) :
    embedDegree n (gradedDifferential x S n v) =
      differential x S (embedDegree (n + 1) v) :=
  LinearMap.congr_fun (embedDegree_gradedDifferential x S n) v

/-- Consecutive degree maps compose to zero for square-zero generators
in characteristic two. No exactness hypothesis is used. -/
theorem gradedDifferential_comp [DecidableEq ι] [CharP A 2]
    (x : ι → A) (S : Finset ι) (hx : ∀ i ∈ S, x i * x i = 0) (n : ℕ) :
    (gradedDifferential x S n).comp (gradedDifferential x S (n + 1)) = 0 := by
  apply LinearMap.ext
  intro v
  apply embedDegree_injective n
  change embedDegree n (gradedDifferential x S n (gradedDifferential x S (n + 1) v)) =
    embedDegree n 0
  rw [map_zero, embedDegree_gradedDifferential_apply, embedDegree_gradedDifferential_apply]
  simpa only [Module.End.mul_apply, LinearMap.zero_apply] using
    LinearMap.congr_fun (differential_square_zero x S hx) (embedDegree (n + 2) v)

/-- Projection of lowering uses only the preceding homogeneous degree. -/
theorem projectDegree_lower (x : ι → A) (i : ι) (n : ℕ) :
    (projectDegree n).comp (lower x i) =
      (gradedLower x i n).comp (projectDegree (n + 1)) := by
  apply Finsupp.lhom_ext
  intro a c
  by_cases hi : a i = 0
  · by_cases ha : a.degree = n + 1 <;>
      simp [LinearMap.comp_apply, projectDegree_single, hi, ha]
  · have hd := degree_sub_single_one_add a i hi
    by_cases ha : a.degree = n + 1
    · have hl : (a - Finsupp.single i 1).degree = n := by omega
      simp [LinearMap.comp_apply, projectDegree_single, hi, ha, hl, lowerIndex]
    · have hl : (a - Finsupp.single i 1).degree ≠ n := by omega
      simp [LinearMap.comp_apply, projectDegree_single, hi, ha, hl]

@[simp] theorem projectDegree_lower_apply (x : ι → A) (i : ι) (n : ℕ)
    (v : Space ι A) :
    projectDegree n (lower x i v) = gradedLower x i n (projectDegree (n + 1) v) :=
  LinearMap.congr_fun (projectDegree_lower x i n) v

/-- Homogeneous projection intertwines the actual differentials. -/
theorem projectDegree_differential (x : ι → A) (S : Finset ι) (n : ℕ) :
    (projectDegree n).comp (differential x S) =
      (gradedDifferential x S n).comp (projectDegree (n + 1)) := by
  apply LinearMap.ext
  intro v
  simp only [LinearMap.comp_apply, gradedDifferential, differential,
    LinearMap.sum_apply, map_sum, projectDegree_lower_apply]

@[simp] theorem projectDegree_differential_apply
    (x : ι → A) (S : Finset ι) (n : ℕ) (v : Space ι A) :
    projectDegree n (differential x S v) =
      gradedDifferential x S n (projectDegree (n + 1) v) :=
  LinearMap.congr_fun (projectDegree_differential x S n) v

/-- An ungraded boundary witness yields a witness in the correct adjacent degree. -/
theorem exists_graded_preimage_of_ungraded_preimage
    (x : ι → A) (S : Finset ι) (n : ℕ) (v : DegreeSpace ι A n)
    (hv : ∃ w : Space ι A, differential x S w = embedDegree n v) :
    ∃ w : DegreeSpace ι A (n + 1), gradedDifferential x S n w = v := by
  obtain ⟨w, hw⟩ := hv
  refine ⟨projectDegree (n + 1) w, ?_⟩
  rw [← projectDegree_differential_apply, hw, projectDegree_embedDegree_apply]

end Kourovka2135.PeriodicResolution
