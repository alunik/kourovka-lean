import Kourovka2135.SLTwoRowSections
import Mathlib.RepresentationTheory.Irreducible

/-! A concrete homogeneous-function embedding from an invariant functional.

The value at a nonzero vector is obtained by applying the functional after
the explicit SL2 matrix with that second row. Left-unipotent invariance
makes this independent of the section. The inverse torus character gives
positive homogeneous weight, and right multiplication supplies full SL2
equivariance for transpose-precomposition. No dimension or classification
hypothesis is used.
-/

set_option autoImplicit false
noncomputable section
universe u v w

namespace Kourovka2135.SLTwoHomogeneousEmbedding

open SLTwoHomogeneousFunctions SLTwoRowSections

variable (k : Type u) [Field k] {F : Type v} [Field F]
variable {V : Type w} [AddCommGroup V] [Module k V]
variable (ρ : Representation k (SLTwo.SL2 F) V) (ell : Module.Dual k V)

/-- Evaluation after the explicit matrix with the requested second row. -/
def rawEvaluation : V →ₗ[k] (Point F → k) :=
  LinearMap.pi (fun z => ell.comp (ρ (rowSection z)))

@[simp] theorem rawEvaluation_apply (v : V) (z : Point F) :
    rawEvaluation k ρ ell v z = ell (ρ (rowSection z) v) := rfl

/-- Unipotent invariance removes the choice of section from every matrix row. -/
theorem rawEvaluation_row
    (hU : ∀ (t : F) (v : V), ell (ρ (SLTwo.uni t) v) = ell v)
    (g : SLTwo.SL2 F) (v : V) :
    rawEvaluation k ρ ell v (pointAction g (infinity F)) = ell (ρ g v) := by
  obtain ⟨t, ht⟩ := exists_uni_mul_rowSection g
  symm
  calc
    ell (ρ g v) = ell (ρ (SLTwo.uni t * rowSection (pointAction g (infinity F))) v) :=
      congrArg (fun x : SLTwo.SL2 F => ell (ρ x v)) ht
    _ = ell (ρ (rowSection (pointAction g (infinity F))) v) := by
      rw [map_mul]
      exact hU t (ρ (rowSection (pointAction g (infinity F))) v)

variable (σ : F →+* k) (n : ℕ)

/-- The inverse torus character gives positive homogeneity in the point variable. -/
theorem rawEvaluation_homogeneous
    (hU : ∀ (t : F) (v : V), ell (ρ (SLTwo.uni t) v) = ell v)
    (hT : ∀ (a : Fˣ) (v : V),
      ell (ρ (SLTwo.tor a) v) = σ ((a⁻¹ : Fˣ) : F) ^ n * ell v)
    (v : V) (a : Fˣ) (z : Point F) :
    rawEvaluation k ρ ell v (scalePoint a z) = σ (a : F) ^ n * rawEvaluation k ρ ell v z := by
  have hrow : pointAction (SLTwo.tor a⁻¹ * rowSection z) (infinity F) = scalePoint a z := by
    rw [point_torus_mul, rowSection_point]
  rw [← hrow, rawEvaluation_row k ρ ell hU, map_mul]
  change ell (ρ (SLTwo.tor a⁻¹) (ρ (rowSection z) v)) =
    σ (a : F) ^ n * ell (ρ (rowSection z) v)
  simpa only [inv_inv] using hT a⁻¹ (ρ (rowSection z) v)

/-- The constructed linear map has values in the actual homogeneous-function subspace. -/
def linearMap
    (hU : ∀ (t : F) (v : V), ell (ρ (SLTwo.uni t) v) = ell v)
    (hT : ∀ (a : Fˣ) (v : V),
      ell (ρ (SLTwo.tor a) v) = σ ((a⁻¹ : Fˣ) : F) ^ n * ell v) :
    V →ₗ[k] Carrier k σ n :=
  (rawEvaluation k ρ ell).codRestrict (space k σ n)
    (fun v => rawEvaluation_homogeneous k ρ ell σ n hU hT v)

variable (hU : ∀ (t : F) (v : V), ell (ρ (SLTwo.uni t) v) = ell v)
variable (hT : ∀ (a : Fˣ) (v : V),
  ell (ρ (SLTwo.tor a) v) = σ ((a⁻¹ : Fˣ) : F) ^ n * ell v)

@[simp] theorem linearMap_apply (v : V) (z : Point F) :
    linearMap k ρ ell σ n hU hT v z = ell (ρ (rowSection z) v) := rfl

/-- Evaluation at infinity recovers the original functional exactly. -/
@[simp] theorem linearMap_infinity (v : V) :
    linearMap k ρ ell σ n hU hT v (infinity F) = ell v := by
  change rawEvaluation k ρ ell v (infinity F) = ell v
  simpa only [pointAction_one, map_one, Module.End.one_apply] using
    rawEvaluation_row k ρ ell hU 1 v

/-- Right matrix multiplication gives the genuine left action on homogeneous functions. -/
theorem linearMap_action (g : SLTwo.SL2 F) (v : V) :
    linearMap k ρ ell σ n hU hT (ρ g v) =
      representation k σ n g (linearMap k ρ ell σ n hU hT v) := by
  apply Subtype.ext
  funext z
  have hrow := rawEvaluation_row k ρ ell hU (rowSection z * g) v
  rw [pointAction_mul, rowSection_point, map_mul] at hrow
  exact hrow.symm

/-- A genuine intertwining map from the original module into the principal series. -/
def embedding : Representation.IntertwiningMap ρ (representation k σ n) :=
  (linearMap k ρ ell σ n hU hT).intertwiningMap_of_isIntertwiningMap
    ρ (representation k σ n) (linearMap_action k ρ ell σ n hU hT)

@[simp] theorem embedding_apply (v : V) :
    embedding k ρ ell σ n hU hT v = linearMap k ρ ell σ n hU hT v := rfl

@[simp] theorem embedding_infinity (v : V) :
    embedding k ρ ell σ n hU hT v (infinity F) = ell v :=
  linearMap_infinity k ρ ell σ n hU hT v

/-- A nonzero invariant functional produces a nonzero actual intertwining map. -/
theorem embedding_ne_zero (hell : ell ≠ 0) : embedding k ρ ell σ n hU hT ≠ 0 := by
  intro h
  apply hell
  apply LinearMap.ext
  intro v
  have hv : embedding k ρ ell σ n hU hT v (infinity F) = 0 := by
    rw [h]
    rfl
  change ell v = 0
  simpa only [embedding_infinity] using hv

/-- Irreducibility turns the constructed nonzero map into an injection, without dimension bounds. -/
theorem embedding_injective [ρ.IsIrreducible] (hell : ell ≠ 0) :
    Function.Injective (embedding k ρ ell σ n hU hT) :=
  (Representation.IsIrreducible.injective_or_eq_zero (embedding k ρ ell σ n hU hT)).resolve_right
    (embedding_ne_zero k ρ ell σ n hU hT hell)

end Kourovka2135.SLTwoHomogeneousEmbedding
