import Kourovka2135.BinaryCochainComplex
import Kourovka2135.HomologyCoordinateInjection
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! Positive-degree homology is detected by the actual surviving monomials.

The coordinate map and boundary detector come from the proved cochain block
contraction. No exactness or detection hypothesis is assumed in the dimension
bound for this particular coefficient complex.
-/

set_option autoImplicit false
noncomputable section
universe u

namespace Kourovka2135.BinaryCochainDimension

open CategoryTheory BinaryCochainGraded BinaryCochainComplex
open scoped IsMulCommutative

variable (k : Type u) [Field k] [CharP k 2] {f : ℕ} (I : Finset (Fin f))

instance survivorIndexFintype (n : ℕ) : Fintype (SurvivorIndex I n) :=
  Fintype.ofFinite _

/-- The actual adjacent-degree short complex centered at positive degree `n+1`. -/
abbrev degreeShortComplex (n : ℕ) : ShortComplex (ModuleCat.{u} k) :=
  (complex k I).sc' n (n + 1) (n + 2)

@[simp] theorem degreeShortComplex_f_hom (n : ℕ) :
    (degreeShortComplex k I n).f.hom = differential k I n := by
  change ((complex k I).d n (n + 1)).hom = _
  exact congrArg ModuleCat.Hom.hom (complex_d k I n)

@[simp] theorem degreeShortComplex_g_hom (n : ℕ) :
    (degreeShortComplex k I n).g.hom = differential k I (n + 1) := by
  change ((complex k I).d (n + 1) (n + 2)).hom = _
  exact congrArg ModuleCat.Hom.hom (complex_d k I (n + 1))

/-- The actual surviving-coordinate map vanishes on the incoming differential. -/
theorem survivorMap_comp_f (n : ℕ) :
    (survivorMap k I (n + 1)).comp (degreeShortComplex k I n).f.hom = 0 := by
  rw [degreeShortComplex_f_hom]
  apply LinearMap.ext
  intro v
  exact survivorMap_differential k I n v

/-- The previously constructed contraction discharges the complete boundary detector. -/
theorem survivorMap_detects_boundaries (n : ℕ) (x : (degreeShortComplex k I n).X₂)
    (hx : (degreeShortComplex k I n).g.hom x = 0)
    (hq : survivorMap k I (n + 1) x = 0) :
    ∃ u : (degreeShortComplex k I n).X₁, (degreeShortComplex k I n).f.hom u = x := by
  rw [degreeShortComplex_g_hom] at hx
  rw [degreeShortComplex_f_hom]
  exact exists_boundary_of_cycle_of_survivorMap_eq_zero k I n x hx hq

/-- Surviving monomial coordinates on the local short-complex homology. -/
def shortHomologyCoordinate (n : ℕ) :
    (degreeShortComplex k I n).homology →ₗ[k] (SurvivorIndex I (n + 1) → k) :=
  HomologyCoordinateInjection.homologyCoordinate (degreeShortComplex k I n)
    (survivorMap k I (n + 1)) (survivorMap_comp_f k I n)

theorem shortHomologyCoordinate_injective (n : ℕ) :
    Function.Injective (shortHomologyCoordinate k I n) :=
  HomologyCoordinateInjection.homologyCoordinate_injective (degreeShortComplex k I n)
    (survivorMap k I (n + 1)) (survivorMap_comp_f k I n)
    (survivorMap_detects_boundaries k I n)

/-- The explicit identification of complex homology with its adjacent-degree short complex. -/
def homologyShortIso (n : ℕ) :
    (complex k I).homology (n + 1) ≅ (degreeShortComplex k I n).homology :=
  (complex k I).homologyIsoSc' n (n + 1) (n + 2) (by simp) (by simp)

/-- An actual linear injection of positive-degree homology into the surviving coordinates. -/
def homologyCoordinate (n : ℕ) :
    (complex k I).homology (n + 1) →ₗ[k] (SurvivorIndex I (n + 1) → k) :=
  (shortHomologyCoordinate k I n).comp (homologyShortIso k I n).hom.hom

theorem homologyCoordinate_injective (n : ℕ) :
    Function.Injective (homologyCoordinate k I n) :=
  (shortHomologyCoordinate_injective k I n).comp (homologyShortIso k I n).toLinearEquiv.injective

/-- Finiteness is obtained from the proved injection, without a finite-homology premise. -/
theorem finiteDimensional_homology (n : ℕ) :
    FiniteDimensional k ((complex k I).homology (n + 1)) :=
  FiniteDimensional.of_injective (homologyCoordinate k I n)
    (homologyCoordinate_injective k I n)

/-- The actual positive-degree homology is bounded by the surviving outside monomials. -/
theorem finrank_homology_le (n : ℕ) :
    Module.finrank k ((complex k I).homology (n + 1)) ≤
      Fintype.card (SurvivorIndex I (n + 1)) := by
  calc
    Module.finrank k ((complex k I).homology (n + 1)) ≤
        Module.finrank k (SurvivorIndex I (n + 1) → k) :=
      LinearMap.finrank_le_finrank_of_injective (homologyCoordinate_injective k I n)
    _ = Fintype.card (SurvivorIndex I (n + 1)) := Module.finrank_fintype_fun_eq_card k

end Kourovka2135.BinaryCochainDimension
