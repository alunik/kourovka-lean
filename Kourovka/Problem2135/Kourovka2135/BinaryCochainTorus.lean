import Kourovka2135.BinaryTensorTorus
import Kourovka2135.BinaryCochainCoordinates

/-! Concrete diagonal cochain operators and their conserved block weights.

The operator is constructed as an actual scalar automorphism on each defect
block and transported to the coefficient cochains. Its basis formula is the
coefficient weight divided by the exponent weight. The scalar is constant
within each block, so it commutes with the differential, homotopy, and
survivor projection. No group-cohomology naturality statement is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.BinaryCochainTorus

open BinaryDefectWeight BinaryTensorSubsetBasis BinaryCochainCoordinates
open scoped IsMulCommutative

variable (k : Type*) [CommRing k] {f : ℕ} (I : Finset (Fin f))

/-- The diagonal weight of an exponent vector. -/
def exponentWeight (c : Fin f → kˣ) (a : Fin f →₀ ℕ) : kˣ :=
  ∏ i : Fin f, c i ^ a i

/-- The cochain weight before regrouping into conserved defect blocks. -/
def cochainWeight (ell : kˣ) (c : Fin f → kˣ) (a : Fin f →₀ ℕ) (J : Subsets I) : kˣ :=
  BinaryTensorTorus.weight k I ell c J / exponentWeight k c a

/-- The weight is constant on the entire block with defect `w`. -/
def blockWeight (ell : kˣ) (c : Fin f → kˣ) (w : Fin f →₀ ℕ) : kˣ :=
  (ell * ∏ i ∈ I, c i) / exponentWeight k c w

theorem exponentWeight_defect (c : Fin f → kˣ) (a : Fin f →₀ ℕ)
    (J : Finset (Fin f)) :
    exponentWeight k c (defectWeight I a J) =
      exponentWeight k c a * ∏ i ∈ I \ J, c i := by
  calc
    exponentWeight k c (defectWeight I a J) =
        ∏ i : Fin f, c i ^ a i * (if i ∈ I \ J then c i else 1) := by
      apply Finset.prod_congr rfl
      intro i _
      by_cases hi : i ∈ I \ J <;> simp [defectWeight_apply, pow_add, hi]
    _ = exponentWeight k c a * ∏ i ∈ I \ J, c i := by
      rw [Finset.prod_mul_distrib, Finset.prod_ite_mem_eq]
      rfl

/-- The exponent defect exactly compensates for the omitted coefficient indices. -/
theorem blockWeight_defect (ell : kˣ) (c : Fin f → kˣ)
    (a : Fin f →₀ ℕ) (J : Subsets I) :
    blockWeight k I ell c (defectWeight I a J.val) = cochainWeight k I ell c a J := by
  rw [blockWeight, exponentWeight_defect, cochainWeight, BinaryTensorTorus.weight,
    ← Finset.prod_sdiff J.property]
  simp [div_eq_mul_inv, mul_assoc, mul_comm]

/-- Scalar multiplication by a unit on each actual defect block. -/
def blockDiagonal (ell : kˣ) (c : Fin f → kˣ) :
    BinaryCochainBlocks.Space I k ≃ₗ[k] BinaryCochainBlocks.Space I k :=
  DFinsupp.mapRange.linearEquiv fun w =>
    LinearEquiv.smulOfUnit (R := k)
      (M := SquarefreeBlock.Space (activeSet I w) k) (blockWeight k I ell c w)

@[simp] theorem blockDiagonal_apply (ell : kˣ) (c : Fin f → kˣ)
    (v : BinaryCochainBlocks.Space I k) (w : Fin f →₀ ℕ) :
    blockDiagonal k I ell c v w = (blockWeight k I ell c w : k) • v w := rfl

theorem blockDiagonal_single (ell : kˣ) (c : Fin f → kˣ) (w : Fin f →₀ ℕ)
    (v : SquarefreeBlock.Space (activeSet I w) k) :
    blockDiagonal k I ell c (DFinsupp.single w v) =
      DFinsupp.single w ((blockWeight k I ell c w : k) • v) := by
  have hs (u : Fin f →₀ ℕ) (z : SquarefreeBlock.Space (activeSet I u) k) :
      LinearEquiv.smulOfUnit (R := k)
          (M := SquarefreeBlock.Space (activeSet I u) k) (blockWeight k I ell c u) z =
        (blockWeight k I ell c u : k) • z := rfl
  simpa only [blockDiagonal, DFinsupp.mapRange.linearEquiv_apply, hs] using
    (DFinsupp.mapRange_single
      (f := fun u z => LinearEquiv.smulOfUnit (R := k)
        (M := SquarefreeBlock.Space (activeSet I u) k) (blockWeight k I ell c u) z)
      (hf := fun _ => map_zero _) (i := w) (b := v))

/-- Any componentwise k-linear map commutes with these block scalars. -/
theorem blockDiagonal_mapRange (ell : kˣ) (c : Fin f → kˣ)
    (F : ∀ w : Fin f →₀ ℕ, Module.End k (SquarefreeBlock.Space (activeSet I w) k))
    (v : BinaryCochainBlocks.Space I k) :
    blockDiagonal k I ell c (DFinsupp.mapRange.linearMap F v) =
      DFinsupp.mapRange.linearMap F (blockDiagonal k I ell c v) := by
  apply DFinsupp.ext
  intro w
  change (blockWeight k I ell c w : k) • F w (v w) =
    F w ((blockWeight k I ell c w : k) • v w)
  exact (map_smul (F w) _ _).symm

theorem blockDiagonal_differential (ell : kˣ) (c : Fin f → kˣ)
    (v : BinaryCochainBlocks.Space I k) :
    blockDiagonal k I ell c (BinaryCochainBlocks.differential k I v) =
      BinaryCochainBlocks.differential k I (blockDiagonal k I ell c v) :=
  blockDiagonal_mapRange k I ell c
    (fun w => SquarefreeBlock.differential k (activeSet I w)) v

theorem blockDiagonal_homotopy (ell : kˣ) (c : Fin f → kˣ)
    (v : BinaryCochainBlocks.Space I k) :
    blockDiagonal k I ell c (BinaryCochainBlocks.homotopy k I v) =
      BinaryCochainBlocks.homotopy k I (blockDiagonal k I ell c v) :=
  blockDiagonal_mapRange k I ell c (BinaryCochainBlocks.blockHomotopy k I) v

theorem blockDiagonal_survivorProjection (ell : kˣ) (c : Fin f → kˣ)
    (v : BinaryCochainBlocks.Space I k) :
    blockDiagonal k I ell c (BinaryCochainBlocks.survivorProjection k I v) =
      BinaryCochainBlocks.survivorProjection k I (blockDiagonal k I ell c v) :=
  blockDiagonal_mapRange k I ell c
    (fun w => if activeSet I w = ∅ then LinearMap.id else 0) v

/-- The actual invertible operator on coefficient cochains. -/
def diagonal (ell : kˣ) (c : Fin f → kˣ) : Cochains k I ≃ₗ[k] Cochains k I :=
  ((coordinates k I).trans (blockDiagonal k I ell c)).trans (coordinates k I).symm

@[simp] theorem coordinates_diagonal (ell : kˣ) (c : Fin f → kˣ) (v : Cochains k I) :
    coordinates k I (diagonal k I ell c v) = blockDiagonal k I ell c (coordinates k I v) := by
  simp only [diagonal, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]

/-- The coordinate formula exposes the single scalar on each conserved block. -/
theorem coordinates_diagonal_apply (ell : kˣ) (c : Fin f → kˣ) (v : Cochains k I)
    (w : Fin f →₀ ℕ) :
    coordinates k I (diagonal k I ell c v) w =
      (blockWeight k I ell c w : k) • coordinates k I v w := by
  rw [coordinates_diagonal, blockDiagonal_apply]

/-- On the actual ground-ring basis, the operator has the expected quotient weight. -/
theorem diagonal_single_basis (ell : kˣ) (c : Fin f → kˣ)
    (a : Fin f →₀ ℕ) (J : Subsets I) :
    diagonal k I ell c (Finsupp.single a (basis k I J)) =
      (cochainWeight k I ell c a J : k) • Finsupp.single a (basis k I J) := by
  apply (coordinates k I).injective
  have hc := coordinates_single k I a J (1 : k)
  simp only [one_smul] at hc
  rw [coordinates_diagonal, map_smul, hc, blockDiagonal_single, blockWeight_defect]
  exact DFinsupp.single_smul _ _

theorem diagonal_groundBasis (ell : kˣ) (c : Fin f → kˣ) (z : CochainIndex I) :
    diagonal k I ell c (groundBasis k I z) =
      (cochainWeight k I ell c z.1 z.2 : k) • groundBasis k I z := by
  rcases z with ⟨a, J⟩
  rw [groundBasis_apply]
  exact diagonal_single_basis k I ell c a J

variable [CharP k 2]

/-- The concrete cochain differential commutes with the diagonal operator. -/
theorem diagonal_differential (ell : kˣ) (c : Fin f → kˣ) (v : Cochains k I) :
    diagonal k I ell c
        (CochainRaising.differential (coefficientGenerator k I) Finset.univ v) =
      CochainRaising.differential (coefficientGenerator k I) Finset.univ
        (diagonal k I ell c v) := by
  apply (coordinates k I).injective
  rw [coordinates_diagonal, coordinates_differential, coordinates_differential,
    coordinates_diagonal]
  exact blockDiagonal_differential k I ell c (coordinates k I v)

theorem diagonal_homotopy (ell : kˣ) (c : Fin f → kˣ) (v : Cochains k I) :
    diagonal k I ell c (BinaryCochainCoordinates.homotopy k I v) =
      BinaryCochainCoordinates.homotopy k I (diagonal k I ell c v) := by
  apply (coordinates k I).injective
  simp only [BinaryCochainCoordinates.homotopy, LinearMap.comp_apply, LinearEquiv.coe_coe,
    coordinates_diagonal, LinearEquiv.apply_symm_apply]
  exact blockDiagonal_homotopy k I ell c (coordinates k I v)

theorem diagonal_survivorProjection (ell : kˣ) (c : Fin f → kˣ) (v : Cochains k I) :
    diagonal k I ell c (BinaryCochainCoordinates.survivorProjection k I v) =
      BinaryCochainCoordinates.survivorProjection k I (diagonal k I ell c v) := by
  apply (coordinates k I).injective
  simp only [BinaryCochainCoordinates.survivorProjection, LinearMap.comp_apply,
    LinearEquiv.coe_coe, coordinates_diagonal, LinearEquiv.apply_symm_apply]
  exact blockDiagonal_survivorProjection k I ell c (coordinates k I v)

end Kourovka2135.BinaryCochainTorus
