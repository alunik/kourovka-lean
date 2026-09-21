import Kourovka2135.HomologyCoordinateInjection
import Mathlib.Algebra.Category.ModuleCat.EpiMono

/-! Naturality of the actual homology-coordinate map.

Equivariance is proved from the coordinate equality on the middle cochain
module. The proof uses the canonical homology projection and its naturality;
no equivariance premise on a final homology injection is assumed.
-/

set_option autoImplicit false
noncomputable section
universe u v w w'

namespace Kourovka2135.HomologyCoordinateEquivariance

open CategoryTheory HomologyCoordinateInjection

variable {k : Type u} [Ring k]
variable (S : ShortComplex (ModuleCat.{v} k))
variable {W : Type w} [AddCommGroup W] [Module k W]
variable (q : S.X₂ →ₗ[k] W) (hq : q.comp S.f.hom = 0)

/-- The quotient-defined coordinate map evaluates a homology class by its cycle coordinates. -/
theorem homologyCoordinate_homologyπ (x : S.cycles) :
    homologyCoordinate S q hq (S.homologyπ.hom x) = q (S.iCycles.hom x) := by
  have hπ : S.moduleCatHomologyIso.hom.hom (S.homologyπ.hom x) =
      (LinearMap.range S.moduleCatToCycles).mkQ (S.moduleCatCyclesIso.hom.hom x) := by
    exact congrArg
      (fun φ : S.cycles ⟶ S.moduleCatLeftHomologyData.H => φ.hom x)
      S.π_moduleCatCyclesIso_hom
  have hi : (S.moduleCatCyclesIso.hom.hom x).val = S.iCycles.hom x := by
    exact congrArg (fun φ : S.cycles ⟶ S.X₂ => φ.hom x) S.moduleCatCyclesIso_hom_i
  change quotientCoordinate S q hq
    (S.moduleCatHomologyIso.hom.hom (S.homologyπ.hom x)) = q (S.iCycles.hom x)
  rw [hπ]
  change q (S.moduleCatCyclesIso.hom.hom x).val = q (S.iCycles.hom x)
  exact congrArg q hi

variable (S' : ShortComplex (ModuleCat.{v} k))
variable {W' : Type w'} [AddCommGroup W'] [Module k W']
variable (q' : S'.X₂ →ₗ[k] W') (hq' : q'.comp S'.f.hom = 0)

/-- Cochain-level naturality descends through the actual categorical homology map. -/
theorem homologyCoordinate_naturality (τ : S ⟶ S') (D : W →ₗ[k] W')
    (hcoord : q'.comp τ.τ₂.hom = D.comp q) :
    (homologyCoordinate S' q' hq').comp (ShortComplex.homologyMap τ).hom =
      D.comp (homologyCoordinate S q hq) := by
  apply LinearMap.ext
  intro z
  have hsurj : Function.Surjective S.homologyπ :=
    (ModuleCat.epi_iff_surjective S.homologyπ).mp inferInstance
  obtain ⟨x, rfl⟩ := hsurj z
  change homologyCoordinate S' q' hq'
      ((ShortComplex.homologyMap τ).hom (S.homologyπ.hom x)) =
    D (homologyCoordinate S q hq (S.homologyπ.hom x))
  have hmap : (ShortComplex.homologyMap τ).hom (S.homologyπ.hom x) =
      S'.homologyπ.hom ((ShortComplex.cyclesMap τ).hom x) := by
    exact congrArg (fun φ : S.cycles ⟶ S'.homology => φ.hom x)
      (ShortComplex.homologyπ_naturality τ)
  rw [hmap, homologyCoordinate_homologyπ, homologyCoordinate_homologyπ]
  have hi : S'.iCycles.hom ((ShortComplex.cyclesMap τ).hom x) =
      τ.τ₂.hom (S.iCycles.hom x) := by
    exact congrArg (fun φ : S.cycles ⟶ S'.X₂ => φ.hom x) (ShortComplex.cyclesMap_i τ)
  rw [hi]
  exact LinearMap.congr_fun hcoord (S.iCycles.hom x)

/-- The endomorphism specialization used for diagonal torus actions. -/
theorem homologyCoordinate_equivariance (τ : S ⟶ S) (D : W →ₗ[k] W)
    (hcoord : q.comp τ.τ₂.hom = D.comp q) :
    (homologyCoordinate S q hq).comp (ShortComplex.homologyMap τ).hom =
      D.comp (homologyCoordinate S q hq) :=
  homologyCoordinate_naturality S q hq S q hq τ D hcoord

theorem homologyCoordinate_equivariance_apply (τ : S ⟶ S) (D : W →ₗ[k] W)
    (hcoord : q.comp τ.τ₂.hom = D.comp q) (x : S.homology) :
    homologyCoordinate S q hq ((ShortComplex.homologyMap τ).hom x) =
      D (homologyCoordinate S q hq x) :=
  LinearMap.congr_fun (homologyCoordinate_equivariance S q hq τ D hcoord) x

end Kourovka2135.HomologyCoordinateEquivariance
