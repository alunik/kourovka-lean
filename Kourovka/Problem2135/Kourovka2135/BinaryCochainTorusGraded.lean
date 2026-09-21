import Kourovka2135.BinaryCochainTorus
import Kourovka2135.BinaryCochainGraded

/-! Restriction of the concrete diagonal cochain action to homogeneous degrees.

The operator is the actual degree projection of the ungraded diagonal applied
to the degree embedding. Its basis formula proves that the degree embedding
intertwines the action, hence the genuine graded differential commutes with
it. Every surviving coordinate has the explicit conserved block weight.
No group-cohomology naturality statement is assumed here.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.BinaryCochainTorusGraded

open PeriodicResolution BinaryTensorSubsetBasis BinaryCochainGraded
open scoped IsMulCommutative

variable (k : Type*) [CommRing k] [CharP k 2] {f : ℕ} (I : Finset (Fin f))

/-- The ground-ring basis combines a homogeneous exponent and coefficient subset. -/
def groundBasis (n : ℕ) :
    Module.Basis (DegreeIndex (Fin f) n × Subsets I) k (DegreeCochains k I n) :=
  (Finsupp.basis fun _ : DegreeIndex (Fin f) n => basis k I).reindex
    (Equiv.sigmaEquivProd _ _)

@[simp] theorem groundBasis_apply (n : ℕ) (a : DegreeIndex (Fin f) n) (J : Subsets I) :
    groundBasis k I n (a, J) = Finsupp.single a (basis k I J) := by
  simp [groundBasis, Finsupp.coe_basis, Equiv.sigmaEquivProd]

/-- Restrict the actual ungraded diagonal using the degree embedding and projection. -/
def diagonal (ell : kˣ) (c : Fin f → kˣ) (n : ℕ) : Module.End k (DegreeCochains k I n) :=
  ((projectDegree n).restrictScalars k).comp
    ((BinaryCochainTorus.diagonal k I ell c).toLinearMap.comp
      ((embedDegree n).restrictScalars k))

/-- The homogeneous basis has the same eigenvalues as its ungraded image. -/
theorem diagonal_single_basis (ell : kˣ) (c : Fin f → kˣ) (n : ℕ)
    (a : DegreeIndex (Fin f) n) (J : Subsets I) :
    diagonal k I ell c n (Finsupp.single a (basis k I J)) =
      (BinaryCochainTorus.cochainWeight k I ell c a.val J : k) •
        Finsupp.single a (basis k I J) := by
  change (projectDegree n).restrictScalars k
    (BinaryCochainTorus.diagonal k I ell c
      (embedDegree n (Finsupp.single a (basis k I J)))) = _
  rw [embedDegree_single, BinaryCochainTorus.diagonal_single_basis, map_smul]
  congr 1
  change projectDegree n (Finsupp.single a.val (basis k I J)) = _
  rw [← embedDegree_single n a (basis k I J), projectDegree_embedDegree_apply]

/-- The restriction is genuinely invertible because all its basis weights are units. -/
def diagonalEquiv (ell : kˣ) (c : Fin f → kˣ) (n : ℕ) :
    DegreeCochains k I n ≃ₗ[k] DegreeCochains k I n :=
  (groundBasis k I n).equiv
    ((groundBasis k I n).unitsSMul fun z =>
      BinaryCochainTorus.cochainWeight k I ell c z.1.val z.2) (Equiv.refl _)

/-- The basis equivalence is the actual projected ungraded action. -/
theorem diagonalEquiv_toLinearMap (ell : kˣ) (c : Fin f → kˣ) (n : ℕ) :
    (diagonalEquiv k I ell c n).toLinearMap = diagonal k I ell c n := by
  apply (groundBasis k I n).ext
  rintro ⟨a, J⟩
  change (groundBasis k I n).equiv
      ((groundBasis k I n).unitsSMul fun z =>
        BinaryCochainTorus.cochainWeight k I ell c z.1.val z.2) (Equiv.refl _)
      (groundBasis k I n (a, J)) = diagonal k I ell c n (groundBasis k I n (a, J))
  rw [Module.Basis.equiv_apply]
  simp only [Equiv.refl_apply, Module.Basis.unitsSMul_apply, Units.smul_def,
    groundBasis_apply, diagonal_single_basis]

/-- The restriction does not discard any part of the diagonal image. -/
theorem embed_diagonal (ell : kˣ) (c : Fin f → kˣ) (n : ℕ) :
    ((embedDegree n).restrictScalars k).comp (diagonal k I ell c n) =
      (BinaryCochainTorus.diagonal k I ell c).toLinearMap.comp
        ((embedDegree n).restrictScalars k) := by
  apply (groundBasis k I n).ext
  rintro ⟨a, J⟩
  simp only [LinearMap.comp_apply, groundBasis_apply, diagonal_single_basis, map_smul,
    LinearMap.restrictScalars_apply, embedDegree_single,
    BinaryCochainTorus.diagonal_single_basis, LinearEquiv.coe_coe]

@[simp] theorem embed_diagonal_apply (ell : kˣ) (c : Fin f → kˣ) (n : ℕ)
    (v : DegreeCochains k I n) :
    embedDegree n (diagonal k I ell c n v) =
      BinaryCochainTorus.diagonal k I ell c (embedDegree n v) :=
  LinearMap.congr_fun (embed_diagonal k I ell c n) v

/-- Commutation with the actual graded differential. -/
theorem diagonal_differential (ell : kˣ) (c : Fin f → kˣ) (n : ℕ)
    (v : DegreeCochains k I n) :
    diagonal k I ell c (n + 1) (differential k I n v) =
      differential k I n (diagonal k I ell c n v) := by
  apply embedDegree_injective (n + 1)
  rw [embed_diagonal_apply]
  change BinaryCochainTorus.diagonal k I ell c
      (embedDegree (n + 1)
        (CochainRaising.gradedDifferential (BinaryCochainCoordinates.coefficientGenerator k I)
          Finset.univ n v)) =
    embedDegree (n + 1)
      (CochainRaising.gradedDifferential (BinaryCochainCoordinates.coefficientGenerator k I)
        Finset.univ n (diagonal k I ell c n v))
  rw [CochainRaising.embedDegree_gradedDifferential,
    CochainRaising.embedDegree_gradedDifferential, embed_diagonal_apply]
  exact BinaryCochainTorus.diagonal_differential k I ell c (embedDegree n v)

/-- One coefficient of a homogeneous cochain, as a ground-ring linear functional. -/
def coordinate (n : ℕ) (a : DegreeIndex (Fin f) n) (J : Subsets I) :
    DegreeCochains k I n →ₗ[k] k :=
  ((basis k I).coord J).comp (Finsupp.lapply a)

@[simp] theorem coordinate_apply (n : ℕ) (a : DegreeIndex (Fin f) n) (J : Subsets I)
    (v : DegreeCochains k I n) :
    coordinate k I n a J v = (basis k I).repr (v a) J := rfl

/-- Every coefficient is multiplied by its explicit cochain eigenvalue. -/
theorem coordinate_diagonal (ell : kˣ) (c : Fin f → kˣ) (n : ℕ)
    (a : DegreeIndex (Fin f) n) (J : Subsets I) (v : DegreeCochains k I n) :
    coordinate k I n a J (diagonal k I ell c n v) =
      (BinaryCochainTorus.cochainWeight k I ell c a.val J : k) *
        coordinate k I n a J v := by
  have h : (coordinate k I n a J).comp (diagonal k I ell c n) =
      (BinaryCochainTorus.cochainWeight k I ell c a.val J : k) • coordinate k I n a J := by
    apply (groundBasis k I n).ext
    rintro ⟨b, K⟩
    simp only [LinearMap.comp_apply, groundBasis_apply, diagonal_single_basis, map_smul,
      LinearMap.smul_apply]
    by_cases hba : b = a
    · subst b
      by_cases hKJ : K = J
      · subst K
        rfl
      · simp [coordinate_apply, Ne.symm hKJ]
    · simp [coordinate_apply, Ne.symm hba]
  exact LinearMap.congr_fun h v

/-- The actual surviving top-coefficient coordinates carry the block character. -/
theorem survivorMap_diagonal_apply (ell : kˣ) (c : Fin f → kˣ) (n : ℕ)
    (v : DegreeCochains k I n) (a : SurvivorIndex I n) :
    survivorMap k I n (diagonal k I ell c n v) a =
      (BinaryCochainTorus.blockWeight k I ell c a.val.val : k) *
        survivorMap k I n v a := by
  exact coordinate_diagonal k I ell c n a.val (topIndex I) v

end Kourovka2135.BinaryCochainTorusGraded
