import Kourovka2135.BinaryCochainCoordinates

/-! The surviving coordinates detect boundaries in every positive degree
of the actual coefficient cochain complex. The boundary witness is
projected to the correct preceding homogeneous degree. -/
set_option autoImplicit false
noncomputable section
namespace Kourovka2135.BinaryCochainGraded
open PeriodicResolution BinaryCochainCoordinates BinaryTensorSubsetBasis
open scoped IsMulCommutative
variable (k : Type*) [CommRing k] [CharP k 2] {f : ℕ} (I : Finset (Fin f))

abbrev DegreeCochains (n : ℕ) := DegreeSpace (Fin f) (BinaryTensorCoefficient.Carrier k I) n

def differential (n : ℕ) : DegreeCochains k I n →ₗ[k] DegreeCochains k I (n + 1) :=
  (CochainRaising.gradedDifferential (coefficientGenerator k I) Finset.univ n).restrictScalars k

theorem differential_comp (n : ℕ) :
    (differential k I (n + 1)).comp (differential k I n) = 0 := by
  apply LinearMap.ext
  intro v
  apply embedDegree_injective (n + 2)
  change embedDegree (n + 2)
    (CochainRaising.gradedDifferential (coefficientGenerator k I) Finset.univ (n + 1)
      (CochainRaising.gradedDifferential (coefficientGenerator k I) Finset.univ n v)) =
    embedDegree (n + 2) 0
  rw [map_zero, CochainRaising.embedDegree_gradedDifferential,
    CochainRaising.embedDegree_gradedDifferential]
  exact BinaryCochainCoordinates.differential_square_zero k I _

/-- Degree-n exponent vectors using only indices omitted from I. -/
abbrev SurvivorIndex (n : ℕ) := {a : DegreeIndex (Fin f) n // ∀ i ∈ I, a.val i = 0}

instance survivorIndexFinite (n : ℕ) : Finite (SurvivorIndex I n) :=
  inferInstance

/-- The surviving coordinate is the top coefficient of each outside monomial. -/
def survivorMap (n : ℕ) : DegreeCochains k I n →ₗ[k] (SurvivorIndex I n → k) where
  toFun v a := (basis k I).repr (v a.val) (topIndex I)
  map_add' v w := by ext a; simp
  map_smul' c v := by ext a; simp

@[simp] theorem survivorMap_apply (n : ℕ) (v : DegreeCochains k I n) (a : SurvivorIndex I n) :
    survivorMap k I n v a = (basis k I).repr (v a.val) (topIndex I) := rfl

/-- No absent-degree coefficient can obstruct the ungraded contraction. -/
theorem survivor_zero_of_graded_zero (n : ℕ) (v : DegreeCochains k I n)
    (hv : survivorMap k I n v = 0) :
    ∀ a : Fin f →₀ ℕ, (∀ i ∈ I, a i = 0) →
      (basis k I).repr (embedDegree n v a) (topIndex I) = 0 := by
  intro a ha
  by_cases hn : a.degree = n
  · have he : embedDegree n v a = v ⟨a, hn⟩ :=
      Finsupp.mapDomain_apply (degreeIndexEmbedding n).injective v ⟨a, hn⟩
    rw [he]
    exact congrFun hv ⟨⟨a, hn⟩, ha⟩
  · have he : embedDegree n v a = 0 := by
      apply Finsupp.mapDomain_of_notMem_range
      rintro ⟨b, hb⟩
      apply hn
      change b.val = a at hb
      rw [← hb]
      exact b.property
    simp [he]

theorem survivorMap_eq_zero_of_ungraded_zero (n : ℕ) (v : DegreeCochains k I n)
    (hv : survivorProjection k I (embedDegree n v) = 0) :
    survivorMap k I n v = 0 := by
  have hz := (survivorProjection_eq_zero_iff k I (embedDegree n v)).mp hv
  funext a
  have he : embedDegree n v a.val.val = v a.val :=
    Finsupp.mapDomain_apply (degreeIndexEmbedding n).injective v a.val
  simpa only [survivorMap_apply, he, Pi.zero_apply] using hz a.val.val a.property

/-- The coordinate map kills actual boundaries. -/
theorem survivorMap_differential (n : ℕ) (v : DegreeCochains k I n) :
    survivorMap k I (n + 1) (differential k I n v) = 0 := by
  apply survivorMap_eq_zero_of_ungraded_zero
  change survivorProjection k I
    (embedDegree (n + 1)
      (CochainRaising.gradedDifferential (coefficientGenerator k I) Finset.univ n v)) = 0
  rw [CochainRaising.embedDegree_gradedDifferential]
  exact BinaryCochainCoordinates.survivorProjection_differential k I _

/-- In every positive degree, a cycle with zero surviving coordinates is
an actual boundary from the preceding homogeneous degree. -/
theorem exists_boundary_of_cycle_of_survivorMap_eq_zero (n : ℕ)
    (v : DegreeCochains k I (n + 1))
    (hv : differential k I (n + 1) v = 0)
    (hz : survivorMap k I (n + 1) v = 0) :
    ∃ u : DegreeCochains k I n, differential k I n u = v := by
  apply CochainRaising.exists_graded_preimage
  apply BinaryCochainCoordinates.exists_boundary_of_cycle_of_coordinates_zero
  · rw [← CochainRaising.embedDegree_gradedDifferential]
    change embedDegree (n + 2) (differential k I (n + 1) v) = 0
    rw [hv, map_zero]
  · exact survivor_zero_of_graded_zero k I (n + 1) v hz

end Kourovka2135.BinaryCochainGraded
