import Kourovka2135.PeriodicResolutionGraded

/-! The raising form of the cochain differential. These are actual linear
maps on exponent-indexed coefficients, with the corresponding homogeneous
maps and projection identities. Each coordinate is raised once; there is no
exponent multiplicity. -/
set_option autoImplicit false
noncomputable section
namespace Kourovka2135.CochainRaising
open PeriodicResolution
variable {ι : Type*} {A : Type*} [CommRing A]

def raise (x : ι → A) (i : ι) : Module.End A (Space ι A) :=
  Finsupp.linearCombination A fun a => Finsupp.single (a + Finsupp.single i 1) (x i)

@[simp] theorem raise_single (x : ι → A) (i : ι) (a : ι →₀ ℕ) (c : A) :
    raise x i (Finsupp.single a c) = Finsupp.single (a + Finsupp.single i 1) (c * x i) := by
  simp [raise, Finsupp.smul_single, smul_eq_mul]

theorem raise_commute (x : ι → A) (i j : ι) : Commute (raise x i) (raise x j) := by
  change raise x i * raise x j = raise x j * raise x i
  apply Finsupp.lhom_ext
  intro a c
  simp [Module.End.mul_apply, add_left_comm, add_comm,
    mul_left_comm, mul_comm]

theorem raise_mul_self (x : ι → A) (i : ι) (hx : x i * x i = 0) :
    raise x i * raise x i = 0 := by
  apply Finsupp.lhom_ext
  intro a c
  simp [Module.End.mul_apply, mul_assoc, hx]

def differential (x : ι → A) (S : Finset ι) : Module.End A (Space ι A) :=
  ∑ i ∈ S, raise x i

def gradedRaise (x : ι → A) (i : ι) (n : ℕ) :
    DegreeSpace ι A n →ₗ[A] DegreeSpace ι A (n + 1) :=
  Finsupp.linearCombination A fun a => Finsupp.single (raiseIndex i a) (x i)

@[simp] theorem gradedRaise_single (x : ι → A) (i : ι) (n : ℕ)
    (a : DegreeIndex ι n) (c : A) :
    gradedRaise x i n (Finsupp.single a c) = Finsupp.single (raiseIndex i a) (c * x i) := by
  simp [gradedRaise, Finsupp.smul_single, smul_eq_mul]

theorem embedDegree_gradedRaise (x : ι → A) (i : ι) (n : ℕ)
    (v : DegreeSpace ι A n) :
    embedDegree (n + 1) (gradedRaise x i n v) = raise x i (embedDegree n v) := by
  suffices h : (embedDegree (n + 1)).comp (gradedRaise x i n) =
      (raise x i).comp (embedDegree n) from LinearMap.congr_fun h v
  apply Finsupp.lhom_ext
  intro a c
  simp

theorem projectDegree_raise (x : ι → A) (i : ι) (n : ℕ)
    (v : Space ι A) :
    projectDegree (n + 1) (raise x i v) = gradedRaise x i n (projectDegree n v) := by
  suffices h : (projectDegree (n + 1)).comp (raise x i) =
      (gradedRaise x i n).comp (projectDegree n) from LinearMap.congr_fun h v
  apply Finsupp.lhom_ext
  intro a c
  by_cases ha : a.degree = n
  · simp [LinearMap.comp_apply, projectDegree_single, ha, raiseIndex]
  · simp [LinearMap.comp_apply, projectDegree_single, ha]

def gradedDifferential (x : ι → A) (S : Finset ι) (n : ℕ) :
    DegreeSpace ι A n →ₗ[A] DegreeSpace ι A (n + 1) :=
  ∑ i ∈ S, gradedRaise x i n

theorem embedDegree_gradedDifferential (x : ι → A) (S : Finset ι) (n : ℕ)
    (v : DegreeSpace ι A n) :
    embedDegree (n + 1) (gradedDifferential x S n v) = differential x S (embedDegree n v) := by
  simp only [gradedDifferential, differential, LinearMap.sum_apply, map_sum,
    embedDegree_gradedRaise]

theorem projectDegree_differential (x : ι → A) (S : Finset ι) (n : ℕ)
    (v : Space ι A) :
    projectDegree (n + 1) (differential x S v) = gradedDifferential x S n (projectDegree n v) := by
  simp only [gradedDifferential, differential, LinearMap.sum_apply, map_sum, projectDegree_raise]

/-- An ungraded cochain boundary in degree n+1 has a homogeneous preimage
in degree n, obtained by actual coefficient projection. -/
theorem exists_graded_preimage (x : ι → A) (S : Finset ι) (n : ℕ)
    (v : DegreeSpace ι A (n + 1))
    (hv : ∃ u : Space ι A, differential x S u = embedDegree (n + 1) v) :
    ∃ u : DegreeSpace ι A n, gradedDifferential x S n u = v := by
  obtain ⟨u, hu⟩ := hv
  refine ⟨projectDegree n u, ?_⟩
  rw [← projectDegree_differential, hu, projectDegree_embedDegree_apply]

end Kourovka2135.CochainRaising
