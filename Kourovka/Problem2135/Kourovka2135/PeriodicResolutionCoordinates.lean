import Kourovka2135.PeriodicResolutionWeight
import Kourovka2135.PeriodicResolutionOperators
import Kourovka2135.PeriodicResolutionBlocks
import Kourovka2135.BinaryExteriorAlgebra
import Mathlib.Data.Finsupp.ToDFinsupp
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.Algebra.CharP.Algebra

/-! Actual coordinates of the exterior-algebra free resolution in its
conserved-weight blocks. The equivalence acts over the ground ring, as the
contracting homotopy need not be linear over the exterior algebra. -/
set_option autoImplicit false
noncomputable section
namespace Kourovka2135.PeriodicResolution
open BinaryExteriorAlgebra
open scoped IsMulCommutative
variable (k : Type*) [CommRing k] (f : ℕ)

/-- The squarefree coefficient basis, followed by the conserved-weight
reindexing, identifies the free module with the actual block direct sum. -/
def blockCoordinates : Space (Fin f) (Carrier k f) ≃ₗ[k]
    PeriodicResolutionBlocks.Space (Fin f) k :=
  (((Finsupp.lcongr (Equiv.refl (Fin f →₀ ℕ)) (basis k f).repr).trans
    (Finsupp.curryLinearEquiv k).symm).trans
    (Finsupp.domLCongr weightIndexEquiv)).trans (sigmaFinsuppLequivDFinsupp k)

theorem blockCoordinates_apply (v : Space (Fin f) (Carrier k f))
    (w : Fin f →₀ ℕ) (J : WeightBlockIndex w) :
    blockCoordinates k f v w J = (basis k f).repr (v (w - subsetIndicator J.val)) J.val := rfl

theorem blockCoordinates_zero_iff (v : Space (Fin f) (Carrier k f)) :
    blockCoordinates k f v 0 = 0 ↔ (basis k f).repr (v 0) ∅ = 0 := by
  constructor
  · intro h
    have hh := congrArg (fun z : SquarefreeBlock.Space (0 : Fin f →₀ ℕ).support k =>
      z ⟨∅, Finset.empty_subset _⟩) h
    simpa [blockCoordinates_apply] using hh
  · intro h
    apply Finsupp.ext
    rintro ⟨J, hJ⟩
    have hJe : J = ∅ := by simpa using hJ
    subst J
    simpa [blockCoordinates_apply] using h

theorem blockCoordinates_single (a : Fin f →₀ ℕ) (J : Finset (Fin f)) (c : k) :
    blockCoordinates k f (Finsupp.single a (c • basis k f J)) =
      DFinsupp.single (blockWeight a J)
        (Finsupp.single ⟨J, subset_le_blockWeight_support a J⟩ c) := by
  simp only [blockCoordinates, LinearEquiv.trans_apply, Finsupp.lcongr_single,
    Equiv.refl_apply, map_smul, Module.Basis.repr_self, Finsupp.smul_single, smul_eq_mul,
    mul_one]
  change sigmaFinsuppLequivDFinsupp k
    (Finsupp.domLCongr weightIndexEquiv
      (Finsupp.single a (Finsupp.single J c)).uncurry) = _
  rw [Finsupp.uncurry_single, Finsupp.domLCongr_single]
  exact sigmaFinsuppEquivDFinsupp_single _ _

/-- The same formula at a prescribed block, with all dependent indices
transported by the proved conserved-weight equality. -/
theorem blockCoordinates_single_of_weight (w a : Fin f →₀ ℕ)
    (J : WeightBlockIndex w) (c : k) (hw : blockWeight a J.val = w) :
    blockCoordinates k f (Finsupp.single a (c • basis k f J.val)) =
      DFinsupp.single w (Finsupp.single J c) := by
  obtain ⟨J, hJ⟩ := J
  change blockWeight a J = w at hw
  subst w
  exact blockCoordinates_single k f a J c

theorem blockCoordinates_symm_single (w : Fin f →₀ ℕ) (J : WeightBlockIndex w) (c : k) :
    (blockCoordinates k f).symm (DFinsupp.single w (Finsupp.single J c)) =
      Finsupp.single (w - subsetIndicator J.val) (c • basis k f J.val) := by
  apply (blockCoordinates k f).injective
  rw [LinearEquiv.apply_symm_apply]
  exact (blockCoordinates_single_of_weight k f w _ J c
    (blockWeight_sub_indicator w J.val J.property)).symm

/-- The standard coefficient basis makes the actual free module a ground-ring
free module as well. -/
def groundBasis : Module.Basis ((Fin f →₀ ℕ) × Finset (Fin f)) k
    (Space (Fin f) (Carrier k f)) :=
  (Finsupp.basis fun _ : Fin f →₀ ℕ => basis k f).reindex (Equiv.sigmaEquivProd _ _)

@[simp] theorem groundBasis_apply (a : Fin f →₀ ℕ) (J : Finset (Fin f)) :
    groundBasis k f (a, J) = Finsupp.single a (basis k f J) := by
  simp [groundBasis, Finsupp.coe_basis, Equiv.sigmaEquivProd]

variable [CharP k 2]

/-- One active column of the differential, evaluated in the actual exterior
algebra. Exterior multiplication inserts an absent squarefree index. -/
theorem lower_single_basis (i : Fin f) (a : Fin f →₀ ℕ) (J : Finset (Fin f)) :
    lower (generator k f) i (Finsupp.single a (basis k f J)) =
      if a i = 0 ∨ i ∈ J then 0 else
        Finsupp.single (a - Finsupp.single i 1) (basis k f (insert i J)) := by
  by_cases ha : a i = 0 <;> by_cases hi : i ∈ J <;>
    simp [lower_single, ha, hi, BinaryExteriorAlgebra.mul_comm, generator_mul_basis]

/-- One blockwise column, extended by zero on blocks without that coordinate. -/
def blockLower (i : Fin f) : Module.End k (PeriodicResolutionBlocks.Space (Fin f) k) :=
  DFinsupp.mapRange.linearMap fun w => if hi : i ∈ w.support then
    SquarefreeBlock.creation k w.support i hi else 0

omit [CharP k 2] in
theorem blockLower_single (i : Fin f) (w : Fin f →₀ ℕ)
    (v : SquarefreeBlock.Space w.support k) :
    blockLower k f i (DFinsupp.single w v) =
      DFinsupp.single w
        ((if hi : i ∈ w.support then SquarefreeBlock.creation k w.support i hi else 0) v) := by
  simpa only [blockLower, DFinsupp.mapRange.linearMap_apply] using
    (DFinsupp.mapRange_single
      (f := fun (u : Fin f →₀ ℕ) z =>
        (if hi : i ∈ u.support then SquarefreeBlock.creation k u.support i hi
          else (0 : Module.End k (SquarefreeBlock.Space u.support k))) z)
      (hf := fun _ => LinearMap.map_zero _) (i := w) (b := v))

omit [CharP k 2] in
theorem blockLower_apply (i : Fin f) (v : PeriodicResolutionBlocks.Space (Fin f) k)
    (w : Fin f →₀ ℕ) :
    blockLower k f i v w =
      (if hi : i ∈ w.support then SquarefreeBlock.creation k w.support i hi else 0) (v w) := rfl

/-- Reindexing identifies every actual algebra-linear column with insertion
in the conserved-weight block. -/
theorem blockCoordinates_lower (i : Fin f) (v : Space (Fin f) (Carrier k f)) :
    blockCoordinates k f (lower (generator k f) i v) =
      blockLower k f i (blockCoordinates k f v) := by
  suffices he : (blockCoordinates k f).toLinearMap.comp
      ((lower (generator k f) i).restrictScalars k) =
      (blockLower k f i).comp (blockCoordinates k f).toLinearMap from
    LinearMap.congr_fun he v
  apply (groundBasis k f).ext
  rintro ⟨a, J⟩
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
    LinearEquiv.coe_coe, groundBasis_apply]
  have hc := blockCoordinates_single k f a J (1 : k)
  simp only [one_smul] at hc
  rw [hc, blockLower_single, lower_single_basis]
  by_cases hi : i ∈ J
  · have hw : i ∈ (blockWeight a J).support := subset_le_blockWeight_support a J hi
    simp [hi]
  · by_cases ha : a i = 0
    · have hw : i ∉ (blockWeight a J).support := by
        simp [Finsupp.mem_support_iff, ha, hi]
      simp [ha, hi]
    · have hw : i ∈ (blockWeight a J).support := by
        simp [Finsupp.mem_support_iff, ha, hi]
      simp only [ha, hi, or_self, ↓reduceIte, dite_eq_left hw,
        SquarefreeBlock.creation_single]
      simpa only [one_smul, hi, ↓reduceIte] using
        blockCoordinates_single_of_weight k f (blockWeight a J)
          (a - Finsupp.single i 1)
          ⟨insert i J, Finset.insert_subset hw (subset_le_blockWeight_support a J)⟩ 1
          (blockWeight_lower_insert a J i ha hi)

omit [CharP k 2] in
/-- Summing columns recovers exactly the finite-support block differential. -/
theorem sum_blockLower :
    (∑ i : Fin f, blockLower k f i) = PeriodicResolutionBlocks.differential k := by
  apply LinearMap.ext
  intro v
  apply DFinsupp.ext
  intro w
  simp only [LinearMap.sum_apply, DFinsupp.finsetSum_apply, blockLower_apply,
    PeriodicResolutionBlocks.differential_apply, SquarefreeBlock.differential,
    LinearMap.sum_apply]
  symm
  rw [Finset.univ_eq_attach, Finset.sum_attach_eq_sum_dite]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> rfl

/-- The explicit ground-ring equivalence intertwines the actual free-module
differential and the proved contractible block differential. -/
theorem blockCoordinates_differential (v : Space (Fin f) (Carrier k f)) :
    blockCoordinates k f (differential (generator k f) Finset.univ v) =
      PeriodicResolutionBlocks.differential k (blockCoordinates k f v) := by
  simp only [differential, LinearMap.sum_apply, map_sum, blockCoordinates_lower]
  simpa only [LinearMap.sum_apply] using
    LinearMap.congr_fun (sum_blockLower k f) (blockCoordinates k f v)

/-- Every cycle in the actual free module with zero augmentation coordinate
has an explicit preimage, supplied by the proved block contraction. -/
theorem exists_boundary_of_cycle_of_zero_coordinate
    (v : Space (Fin f) (Carrier k f))
    (hv : differential (generator k f) Finset.univ v = 0)
    (hzero : (basis k f).repr (v 0) ∅ = 0) :
    ∃ u : Space (Fin f) (Carrier k f),
      differential (generator k f) Finset.univ u = v := by
  refine ⟨(blockCoordinates k f).symm
    (PeriodicResolutionBlocks.homotopy k (blockCoordinates k f v)), ?_⟩
  apply (blockCoordinates k f).injective
  rw [blockCoordinates_differential, LinearEquiv.apply_symm_apply]
  apply PeriodicResolutionBlocks.differential_homotopy_of_cycle
  · rw [← blockCoordinates_differential, hv, map_zero]
  · exact (blockCoordinates_zero_iff k f v).mpr hzero

end Kourovka2135.PeriodicResolution
