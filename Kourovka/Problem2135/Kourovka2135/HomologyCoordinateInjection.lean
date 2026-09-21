import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! Homology detected by actual cycle coordinates.

A linear coordinate map that kills boundaries descends to homology. If its
zero-coordinate cycles are boundaries, the induced map is injective. This
separates the elementary quotient argument from any particular complex.
-/

set_option autoImplicit false
noncomputable section
universe u v w

namespace Kourovka2135.HomologyCoordinateInjection

open CategoryTheory

section Ring

variable {k : Type u} [Ring k]
variable (S : ShortComplex (ModuleCat.{v} k))
variable {W : Type w} [AddCommGroup W] [Module k W]
variable (q : S.X₂ →ₗ[k] W)

/-- Restrict the actual coordinate map to the concrete cycle submodule. -/
def cyclesCoordinate : LinearMap.ker S.g.hom →ₗ[k] W :=
  q.comp (LinearMap.ker S.g.hom).subtype

@[simp] theorem cyclesCoordinate_apply (x : LinearMap.ker S.g.hom) :
    cyclesCoordinate S q x = q x.val := rfl

theorem boundaries_le_ker_cyclesCoordinate (hq : q.comp S.f.hom = 0) :
    LinearMap.range S.moduleCatToCycles ≤ (cyclesCoordinate S q).ker := by
  rintro x ⟨u, rfl⟩
  change q (S.f.hom u) = 0
  exact LinearMap.congr_fun hq u

/-- The descended map on the concrete quotient of cycles by boundaries. -/
def quotientCoordinate (hq : q.comp S.f.hom = 0) :
    (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles) →ₗ[k] W :=
  (LinearMap.range S.moduleCatToCycles).liftQ (cyclesCoordinate S q)
    (boundaries_le_ker_cyclesCoordinate S q hq)

@[simp] theorem quotientCoordinate_mkQ (hq : q.comp S.f.hom = 0)
    (x : LinearMap.ker S.g.hom) :
    quotientCoordinate S q hq ((LinearMap.range S.moduleCatToCycles).mkQ x) = q x.val := rfl

/-- Zero-coordinate cycles being boundaries is exactly the injectivity condition needed here. -/
theorem quotientCoordinate_injective (hq : q.comp S.f.hom = 0)
    (hdetect : ∀ x : S.X₂, S.g.hom x = 0 → q x = 0 →
      ∃ u : S.X₁, S.f.hom u = x) :
    Function.Injective (quotientCoordinate S q hq) := by
  apply LinearMap.ker_eq_bot.mp
  apply Submodule.ker_liftQ_eq_bot
  intro x hx
  have hxq : q x.val = 0 := hx
  obtain ⟨u, hu⟩ := hdetect x.val x.property hxq
  exact ⟨u, Subtype.ext hu⟩

/-- Actual coordinates on the categorical homology object. -/
def homologyCoordinate (hq : q.comp S.f.hom = 0) : S.homology →ₗ[k] W :=
  (quotientCoordinate S q hq).comp S.moduleCatHomologyIso.hom.hom

theorem homologyCoordinate_injective (hq : q.comp S.f.hom = 0)
    (hdetect : ∀ x : S.X₂, S.g.hom x = 0 → q x = 0 →
      ∃ u : S.X₁, S.f.hom u = x) :
    Function.Injective (homologyCoordinate S q hq) := by
  exact (quotientCoordinate_injective S q hq hdetect).comp
    S.moduleCatHomologyIso.toLinearEquiv.injective

end Ring

section Field

variable {k : Type u} [Field k]
variable (S : ShortComplex (ModuleCat.{v} k))
variable {W : Type w} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
variable (q : S.X₂ →ₗ[k] W)

/-- Finite coordinate spaces give finite-dimensional homology. -/
theorem finiteDimensional_homology (hq : q.comp S.f.hom = 0)
    (hdetect : ∀ x : S.X₂, S.g.hom x = 0 → q x = 0 →
      ∃ u : S.X₁, S.f.hom u = x) :
    FiniteDimensional k S.homology :=
  FiniteDimensional.of_injective (homologyCoordinate S q hq)
    (homologyCoordinate_injective S q hq hdetect)

/-- The homology dimension is bounded by the number of surviving coordinates. -/
theorem finrank_homology_le (hq : q.comp S.f.hom = 0)
    (hdetect : ∀ x : S.X₂, S.g.hom x = 0 → q x = 0 →
      ∃ u : S.X₁, S.f.hom u = x) :
    Module.finrank k S.homology ≤ Module.finrank k W :=
  LinearMap.finrank_le_finrank_of_injective (homologyCoordinate_injective S q hq hdetect)

end Field

end Kourovka2135.HomologyCoordinateInjection
