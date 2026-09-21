import Kourovka2135.IsotypicFrattiniMultiplicity

/-! Actual ordinary H2 cannot vanish for a nonzero semisimple isotypic
Frattini kernel. The checked one-copy result gives an actual coefficient
equivalence, whose factor-set class cannot be zero. -/

set_option autoImplicit false
noncomputable section
universe u

namespace Kourovka2135.IsotypicFrattiniVanishing

open Representation AbelianExtensionCocycle IsotypicFrattiniMultiplicity
open scoped MonoidAlgebra

variable {k Q W V : Type u} [Field k] [Group Q] [Finite Q]
variable [AddCommGroup W] [Module k W] [FiniteDimensional k W] [Nontrivial W]
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]
variable (ρW : Representation k Q W) (ρV : Representation k Q V)
variable [IsSemisimpleModule k[Q] ρW.asModule] [ρV.IsIrreducible]
variable {J : Type u} [Group J] [Finite J]
variable (S : GroupExtension (Multiplicative W) J Q)
variable (hcompat : CompatibleAction S ρW)

include hcompat in
/-- A genuine nonzero isotypic Frattini kernel prevents actual H2 vanishing;
there is no assumption of positive cohomology in this statement. -/
theorem not_subsingleton_H2
    (hiso : IsIsotypicOfType k[Q] ρW.asModule ρV.asModule)
    (hΦ : S.inl.range ≤ frattini J) :
    ¬ Subsingleton (groupCohomology (Rep.of ρV) 2) := by
  intro hzero
  let : Subsingleton (groupCohomology (Rep.of ρV) 2) := hzero
  have hH2 : Module.finrank k (groupCohomology (Rep.of ρV) 2) ≤
      Module.finrank k (ρV.IntertwiningMap ρV) := by
    rw [Module.finrank_zero_of_subsingleton]
    exact Nat.zero_le _
  let e := equivOfIsotypicFrattiniH2Bound ρW ρV S hcompat hiso hΦ hH2
  have he : e.toIntertwiningMap = 0 :=
    eq_zero_of_transgression_eq_zero S ρV ρW hcompat hΦ e.toIntertwiningMap
      (Subsingleton.elim _ _)
  let : Nontrivial ρV.asModule :=
    IsSimpleModule.nontrivial k[Q] ρV.asModule
  let : Nontrivial V := ρV.asModuleEquiv.symm.toEquiv.nontrivial
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨w, hw⟩ := e.surjective v
  have hew : e w = 0 :=
    congrArg (fun f : ρW.IntertwiningMap ρV => f w) he
  exact hv (hw.symm.trans hew)

include hcompat in
/-- The nonvanishing conclusion as a genuine nontrivial ordinary-cohomology type. -/
theorem nontrivial_H2
    (hiso : IsIsotypicOfType k[Q] ρW.asModule ρV.asModule)
    (hΦ : S.inl.range ≤ frattini J) :
    Nontrivial (groupCohomology (Rep.of ρV) 2) :=
  not_subsingleton_iff_nontrivial.mp (not_subsingleton_H2 ρW ρV S hcompat hiso hΦ)

end Kourovka2135.IsotypicFrattiniVanishing
