import Kourovka2135.IsotypicTwoCopyQuotient
import Kourovka2135.FrattiniCohomologyMultiplicity

/-! A nonzero semisimple isotypic Frattini kernel is one simple copy when
its actual ordinary H2 has at most one commuting-endomorphism degree.

Semisimplicity and isotypy are explicit properties of the kernel's group-algebra
module. Every group-algebra map is transported to an actual intertwiner.
-/

set_option autoImplicit false
noncomputable section
universe u

namespace Kourovka2135.IsotypicFrattiniMultiplicity

open Representation
open scoped MonoidAlgebra

variable {k Q W V : Type u} [Field k] [Group Q]
variable [AddCommGroup W] [Module k W] [AddCommGroup V] [Module k V]
variable (ρW : Representation k Q W) (ρV : Representation k Q V)

/-- The actual group-algebra linear map, viewed as an equivariant native map. -/
def intertwinerOfModuleMap (f : ρW.asModule →ₗ[k[Q]] ρV.asModule) :
    ρW.IntertwiningMap ρV :=
  (IntertwiningMap.equivLinearMapAsModule ρW ρV).symm f

@[simp] theorem intertwinerOfModuleMap_apply
    (f : ρW.asModule →ₗ[k[Q]] ρV.asModule) (w : W) :
    intertwinerOfModuleMap ρW ρV f w =
      ρV.asModuleEquiv (f (ρW.asModuleEquiv.symm w)) := rfl

/-- Convert a two-copy module map by its actual first and second projections. -/
def prodIntertwinerOfModuleMap
    (f : ρW.asModule →ₗ[k[Q]] ρV.asModule × ρV.asModule) :
    ρW.IntertwiningMap (ρV.prod ρV) :=
  (intertwinerOfModuleMap ρW ρV
    ((LinearMap.fst k[Q] ρV.asModule ρV.asModule).comp f)).prod
      (intertwinerOfModuleMap ρW ρV
        ((LinearMap.snd k[Q] ρV.asModule ρV.asModule).comp f))

@[simp] theorem prodIntertwinerOfModuleMap_apply
    (f : ρW.asModule →ₗ[k[Q]] ρV.asModule × ρV.asModule) (w : W) :
    prodIntertwinerOfModuleMap ρW ρV f w =
      (ρV.asModuleEquiv (f (ρW.asModuleEquiv.symm w)).1,
        ρV.asModuleEquiv (f (ρW.asModuleEquiv.symm w)).2) := rfl

theorem prodIntertwinerOfModuleMap_surjective
    (f : ρW.asModule →ₗ[k[Q]] ρV.asModule × ρV.asModule)
    (hf : Function.Surjective f) :
    Function.Surjective (prodIntertwinerOfModuleMap ρW ρV f) := by
  intro v
  obtain ⟨w, hw⟩ := hf (ρV.asModuleEquiv.symm v.1, ρV.asModuleEquiv.symm v.2)
  refine ⟨ρW.asModuleEquiv w, ?_⟩
  simp only [prodIntertwinerOfModuleMap_apply, LinearEquiv.symm_apply_apply, hw,
    LinearEquiv.apply_symm_apply, Prod.mk.eta]

/-- An actual group-algebra equivalence gives an actual representation equivalence. -/
def equivOfModuleEquiv (e : ρW.asModule ≃ₗ[k[Q]] ρV.asModule) : ρW.Equiv ρV :=
  (intertwinerOfModuleMap ρW ρV e.toLinearMap).ofBijective (by
    change Function.Bijective (fun w => ρV.asModuleEquiv (e (ρW.asModuleEquiv.symm w)))
    exact ρV.asModuleEquiv.bijective.comp (e.bijective.comp ρW.asModuleEquiv.symm.bijective))

variable [Finite Q] [FiniteDimensional k W] [FiniteDimensional k V] [Nontrivial W]
variable [IsSemisimpleModule k[Q] ρW.asModule] [ρV.IsIrreducible]
variable {J : Type u} [Group J] [Finite J]
variable (S : GroupExtension (Multiplicative W) J Q)
variable (hcompat : AbelianExtensionCocycle.CompatibleAction S ρW)

include hcompat in
/-- The actual cohomology bound eliminates the two-copy alternative. -/
theorem nonempty_equiv_of_isotypic_frattini_H2_bound
    (hiso : IsIsotypicOfType k[Q] ρW.asModule ρV.asModule)
    (hΦ : S.inl.range ≤ frattini J)
    (hH2 : Module.finrank k (groupCohomology (Rep.of ρV) 2) ≤
      Module.finrank k (ρV.IntertwiningMap ρV)) : Nonempty (ρW.Equiv ρV) := by
  let : Module.Finite k[Q] ρW.asModule :=
    Module.Finite.of_restrictScalars_finite k k[Q] ρW.asModule
  let : Nontrivial ρW.asModule := ρW.asModuleEquiv.toEquiv.nontrivial
  obtain ⟨e⟩ := IsotypicTwoCopyQuotient.nonempty_linearEquiv_of_no_surjective_prod
    k[Q] ρW.asModule ρV.asModule hiso (by
      intro f hf
      exact FrattiniCohomologyMultiplicity.not_surjective_two_copies_of_H2_le_end
        ρW ρV S hcompat hΦ hH2 (prodIntertwinerOfModuleMap ρW ρV f)
        (prodIntertwinerOfModuleMap_surjective ρW ρV f hf))
  exact ⟨equivOfModuleEquiv ρW ρV e⟩

/-- Choose the actual single-copy equivalence supplied by the proved dichotomy. -/
def equivOfIsotypicFrattiniH2Bound
    (hiso : IsIsotypicOfType k[Q] ρW.asModule ρV.asModule)
    (hΦ : S.inl.range ≤ frattini J)
    (hH2 : Module.finrank k (groupCohomology (Rep.of ρV) 2) ≤
      Module.finrank k (ρV.IntertwiningMap ρV)) : ρW.Equiv ρV :=
  Classical.choice (nonempty_equiv_of_isotypic_frattini_H2_bound ρW ρV S hcompat hiso hΦ hH2)

end Kourovka2135.IsotypicFrattiniMultiplicity
