import Mathlib.CategoryTheory.Abelian.Ext
import Mathlib.CategoryTheory.Linear.LinearFunctor

/-! A fully faithful linear functor identifies the actual Hom complexes of
a chain complex and its image. This supplies the categorical transport
needed after identifying a group algebra with the explicit coordinate algebra. -/
set_option autoImplicit false
noncomputable section
namespace Kourovka2135.LinearFunctorHomComplex
open CategoryTheory
universe u v w v'
variable (k : Type u) [CommRing k]
variable {C : Type v} [Category.{w} C] [Abelian C] [Linear k C]
variable {D : Type v'} [Category.{w} D] [Abelian D] [Linear k D]
variable (F : C ⥤ D) [F.Additive] [F.Linear k] [F.Full] [F.Faithful]

/-- The actual functor map on morphisms is a linear equivalence. -/
def homEquiv (X Y : C) : (X ⟶ Y) ≃ₗ[k] (F.obj X ⟶ F.obj Y) :=
  LinearEquiv.ofBijective (F.mapLinearMap k) ⟨F.map_injective, F.map_surjective⟩

@[simp] theorem homEquiv_apply (X Y : C) (φ : X ⟶ Y) :
    homEquiv k F X Y φ = F.map φ := rfl

/-- Fully faithful linear transport commutes with the entire Hom differential. -/
def complexIso (P : ChainComplex C ℕ) (M : C) :
    P.linearYonedaObj k M ≅
      ChainComplex.linearYonedaObj ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P) k (F.obj M) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (homEquiv k F (P.X n) M).toModuleIso)
    (by
      intro n m _
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro φ
      exact (F.map_comp (P.d m n) φ).symm)

end Kourovka2135.LinearFunctorHomComplex
