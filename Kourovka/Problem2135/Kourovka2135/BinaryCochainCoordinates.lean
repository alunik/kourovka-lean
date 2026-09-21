import Kourovka2135.BinaryDefectWeight
import Kourovka2135.BinaryTensorSubsetBasis
import Kourovka2135.BinaryCochainBlocks
import Kourovka2135.CochainRaising
import Mathlib.Data.Finsupp.ToDFinsupp
import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-! Actual coefficient cochains in their conserved defect blocks. The
coordinate equivalence is linear over the ground ring. Its differential
is the raising differential induced by multiplication in the concrete
coefficient algebra. -/
set_option autoImplicit false
noncomputable section
namespace Kourovka2135.BinaryCochainCoordinates
open BinaryDefectWeight BinaryTensorSubsetBasis
open scoped IsMulCommutative
variable (k : Type*) [CommRing k] {f : ℕ} (I : Finset (Fin f))

abbrev Cochains := PeriodicResolution.Space (Fin f) (BinaryTensorCoefficient.Carrier k I)

def coordinates : Cochains k I ≃ₗ[k] BinaryCochainBlocks.Space I k :=
  (((Finsupp.lcongr (Equiv.refl (Fin f →₀ ℕ)) (basis k I).repr).trans
    (Finsupp.curryLinearEquiv k).symm).trans
    (Finsupp.domLCongr (defectIndexEquiv I))).trans (sigmaFinsuppLequivDFinsupp k)

theorem coordinates_apply (v : Cochains k I) (w : Fin f →₀ ℕ)
    (L : DefectBlockIndex I w) :
    coordinates k I v w L = (basis k I).repr (v (recoveredExponent I w L.val))
      ⟨recoveredSubset I w L.val, recoveredSubset_subset I w L.val L.property⟩ := rfl

theorem coordinates_single (a : Fin f →₀ ℕ) (J : Subsets I) (c : k) :
    coordinates k I (Finsupp.single a (c • basis k I J)) =
      DFinsupp.single (defectWeight I a J.val)
        (Finsupp.single ⟨defectCoordinate I a J.val, defectCoordinate_subset I a J.val⟩ c) := by
  simp only [coordinates, LinearEquiv.trans_apply, Finsupp.lcongr_single,
    Equiv.refl_apply, map_smul, Module.Basis.repr_self, Finsupp.smul_single, smul_eq_mul,
    mul_one]
  change sigmaFinsuppLequivDFinsupp k
    (Finsupp.domLCongr (defectIndexEquiv I)
      (Finsupp.single a (Finsupp.single J c)).uncurry) = _
  rw [Finsupp.uncurry_single, Finsupp.domLCongr_single]
  exact sigmaFinsuppEquivDFinsupp_single _ _

theorem coordinates_single_of_weight (w a : Fin f →₀ ℕ) (J : Subsets I)
    (L : DefectBlockIndex I w) (c : k)
    (hw : defectWeight I a J.val = w) (hL : defectCoordinate I a J.val = L.val) :
    coordinates k I (Finsupp.single a (c • basis k I J)) =
      DFinsupp.single w (Finsupp.single L c) := by
  subst w
  have he : (⟨defectCoordinate I a J.val, defectCoordinate_subset I a J.val⟩ :
      DefectBlockIndex I (defectWeight I a J.val)) = L := Subtype.ext hL
  rw [coordinates_single, he]

def groundBasis : Module.Basis (CochainIndex I) k (Cochains k I) :=
  (Finsupp.basis fun _ : Fin f →₀ ℕ => basis k I).reindex (Equiv.sigmaEquivProd _ _)

@[simp] theorem groundBasis_apply (a : Fin f →₀ ℕ) (J : Subsets I) :
    groundBasis k I (a, J) = Finsupp.single a (basis k I J) := by
  simp [groundBasis, Finsupp.coe_basis, Equiv.sigmaEquivProd]

variable [CharP k 2]

/-- The algebra generators acting on the actual coefficient algebra. -/
def coefficientGenerator (i : Fin f) : BinaryTensorCoefficient.Carrier k I :=
  BinaryTensorCoefficient.projection k I (BinaryExteriorAlgebra.generator k f i)

theorem raise_single_basis (i : Fin f) (a : Fin f →₀ ℕ) (J : Subsets I) :
    CochainRaising.raise (coefficientGenerator k I) i (Finsupp.single a (basis k I J)) =
      if h : i ∈ I ∧ i ∉ J.val then
        Finsupp.single (a + Finsupp.single i 1) (basis k I (insertIndex I i h.1 J)) else 0 := by
  rw [CochainRaising.raise_single, mul_comm]
  change Finsupp.single (a + Finsupp.single i 1)
    (BinaryExteriorAlgebra.generator k f i • basis k I J) = _
  rw [generator_smul_basis]
  split_ifs <;> simp

/-- A raising column becomes squarefree creation in each active defect block. -/
def blockRaise (i : Fin f) : Module.End k (BinaryCochainBlocks.Space I k) :=
  DFinsupp.mapRange.linearMap fun w => if hi : i ∈ activeSet I w then
    SquarefreeBlock.creation k (activeSet I w) i hi else 0

omit [CharP k 2] in
theorem blockRaise_single (i : Fin f) (w : Fin f →₀ ℕ)
    (v : SquarefreeBlock.Space (activeSet I w) k) :
    blockRaise k I i (DFinsupp.single w v) =
      DFinsupp.single w
        ((if hi : i ∈ activeSet I w then SquarefreeBlock.creation k (activeSet I w) i hi
          else 0) v) := by
  simpa only [blockRaise, DFinsupp.mapRange.linearMap_apply] using
    (DFinsupp.mapRange_single
      (f := fun (u : Fin f →₀ ℕ) z =>
        (if hi : i ∈ activeSet I u then SquarefreeBlock.creation k (activeSet I u) i hi
          else (0 : Module.End k (SquarefreeBlock.Space (activeSet I u) k))) z)
      (hf := fun _ => LinearMap.map_zero _) (i := w) (b := v))

omit [CharP k 2] in
theorem blockRaise_apply (i : Fin f) (v : BinaryCochainBlocks.Space I k)
    (w : Fin f →₀ ℕ) :
    blockRaise k I i v w =
      (if hi : i ∈ activeSet I w then SquarefreeBlock.creation k (activeSet I w) i hi else 0)
        (v w) := rfl

theorem coordinates_raise (i : Fin f) (v : Cochains k I) :
    coordinates k I (CochainRaising.raise (coefficientGenerator k I) i v) =
      blockRaise k I i (coordinates k I v) := by
  suffices he : (coordinates k I).toLinearMap.comp
      ((CochainRaising.raise (coefficientGenerator k I) i).restrictScalars k) =
      (blockRaise k I i).comp (coordinates k I).toLinearMap from
    LinearMap.congr_fun he v
  apply (groundBasis k I).ext
  rintro ⟨a, J⟩
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
    LinearEquiv.coe_coe, groundBasis_apply]
  have hc := coordinates_single k I a J (1 : k)
  simp only [one_smul] at hc
  rw [hc, blockRaise_single, raise_single_basis]
  by_cases hi : i ∈ I
  · by_cases hij : i ∈ J.val
    · by_cases hw : i ∈ activeSet I (defectWeight I a J.val)
      · simp [hi, hij, hw, defectCoordinate]
      · simp [hi, hij, hw]
    · have hdiff : i ∈ I \ J.val := Finset.mem_sdiff.mpr ⟨hi, hij⟩
      have hw := sdiff_subset_activeSet I a J.val hdiff
      have hn := notMem_defectCoordinate_of_mem_sdiff I a J.val i hdiff
      simp only [hi, hij, not_false_eq_true, and_self, ↓reduceDIte,
        dite_eq_left hw, SquarefreeBlock.creation_single, hn, ↓reduceIte]
      simpa only [one_smul] using
        coordinates_single_of_weight k I (defectWeight I a J.val)
          (a + Finsupp.single i 1) (insertIndex I i hi J)
          ⟨insert i (defectCoordinate I a J.val),
            Finset.insert_subset hw (defectCoordinate_subset I a J.val)⟩ 1
          (defectWeight_raise_insert I a J.val i hdiff)
          (defectCoordinate_raise_insert I a J.val i hdiff)
  · have hw : i ∉ activeSet I (defectWeight I a J.val) :=
      fun h => hi (activeSet_subset I _ h)
    simp [hi, hw]

omit [CharP k 2] in
theorem sum_blockRaise : (∑ i : Fin f, blockRaise k I i) = BinaryCochainBlocks.differential k I := by
  apply LinearMap.ext
  intro v
  apply DFinsupp.ext
  intro w
  simp only [LinearMap.sum_apply, DFinsupp.finsetSum_apply, blockRaise_apply,
    BinaryCochainBlocks.differential_apply, SquarefreeBlock.differential,
    LinearMap.sum_apply]
  symm
  rw [Finset.univ_eq_attach, Finset.sum_attach_eq_sum_dite]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> rfl

theorem coordinates_differential (v : Cochains k I) :
    coordinates k I (CochainRaising.differential (coefficientGenerator k I) Finset.univ v) =
      BinaryCochainBlocks.differential k I (coordinates k I v) := by
  simp only [CochainRaising.differential, LinearMap.sum_apply, map_sum, coordinates_raise]
  simpa only [LinearMap.sum_apply] using
    LinearMap.congr_fun (sum_blockRaise k I) (coordinates k I v)

/-- Square zero follows from the actual coordinate equivalence and the
proved squarefree-block differential. -/
theorem differential_square_zero (v : Cochains k I) :
    CochainRaising.differential (coefficientGenerator k I) Finset.univ
      (CochainRaising.differential (coefficientGenerator k I) Finset.univ v) = 0 := by
  apply (coordinates k I).injective
  rw [coordinates_differential, coordinates_differential, map_zero]
  exact LinearMap.congr_fun (BinaryCochainBlocks.differential_square_zero k I)
    (coordinates k I v)

/-- The actual cochain contraction retains precisely the inactive defect blocks. -/
def survivorProjection : Module.End k (Cochains k I) :=
  (coordinates k I).symm.toLinearMap.comp
    ((BinaryCochainBlocks.survivorProjection k I).comp (coordinates k I).toLinearMap)

def homotopy : Module.End k (Cochains k I) :=
  (coordinates k I).symm.toLinearMap.comp
    ((BinaryCochainBlocks.homotopy k I).comp (coordinates k I).toLinearMap)

theorem contraction (v : Cochains k I) :
    CochainRaising.differential (coefficientGenerator k I) Finset.univ (homotopy k I v) +
      homotopy k I (CochainRaising.differential (coefficientGenerator k I) Finset.univ v) +
      survivorProjection k I v = v := by
  apply (coordinates k I).injective
  simpa [homotopy, survivorProjection, coordinates_differential] using
    BinaryCochainBlocks.contraction k I (coordinates k I v)

/-- The survivors are exactly top coefficient monomials whose exponent
coordinates in I vanish. Outside exponent coordinates remain unrestricted. -/
theorem survivorProjection_eq_zero_iff (v : Cochains k I) :
    survivorProjection k I v = 0 ↔
      ∀ a : Fin f →₀ ℕ, (∀ i ∈ I, a i = 0) →
        (basis k I).repr (v a) (topIndex I) = 0 := by
  have hzero : survivorProjection k I v = 0 ↔
      BinaryCochainBlocks.survivorProjection k I (coordinates k I v) = 0 := by
    constructor
    · intro h
      have hc := congrArg (coordinates k I) h
      simpa [survivorProjection] using hc
    · intro h
      simp [survivorProjection, h]
  rw [hzero, BinaryCochainBlocks.survivorProjection_eq_zero_iff]
  constructor
  · intro h a ha
    have he : activeSet I a = ∅ := (activeSet_eq_empty_iff I a).mpr ha
    have hc := congrArg
      (fun z : SquarefreeBlock.Space (activeSet I a) k => z ⟨∅, Finset.empty_subset _⟩)
      (h a he)
    simpa [coordinates_apply, recoveredExponent, recoveredSubset, he, topIndex] using hc
  · intro h w hw
    apply Finsupp.ext
    rintro ⟨L, hL⟩
    have he : L = ∅ := by simpa [hw] using hL
    subst L
    simpa [coordinates_apply, recoveredExponent, recoveredSubset, hw, topIndex] using
      h w ((activeSet_eq_empty_iff I w).mp hw)

/-- Every boundary has vanishing surviving coordinates. -/
theorem survivorProjection_differential (v : Cochains k I) :
    survivorProjection k I
      (CochainRaising.differential (coefficientGenerator k I) Finset.univ v) = 0 := by
  apply (coordinates k I).injective
  simp only [survivorProjection, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, coordinates_differential, map_zero]
  exact LinearMap.congr_fun (BinaryCochainBlocks.survivorProjection_differential k I)
    (coordinates k I v)

/-- Every actual cycle with vanishing surviving coordinates is a boundary. -/
theorem exists_boundary_of_cycle_of_coordinates_zero (v : Cochains k I)
    (hv : CochainRaising.differential (coefficientGenerator k I) Finset.univ v = 0)
    (hz : ∀ a : Fin f →₀ ℕ, (∀ i ∈ I, a i = 0) →
      (basis k I).repr (v a) (topIndex I) = 0) :
    ∃ u : Cochains k I,
      CochainRaising.differential (coefficientGenerator k I) Finset.univ u = v := by
  refine ⟨homotopy k I v, ?_⟩
  have hp := (survivorProjection_eq_zero_iff k I v).mpr hz
  simpa [hv, hp] using contraction k I v

end Kourovka2135.BinaryCochainCoordinates
