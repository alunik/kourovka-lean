import Kourovka2135.FrattiniCocycleObstruction
import Kourovka2135.GroupCohomologyFieldExtension
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! An actual Frattini extension bounds the space of equivariant maps from its
kernel by ordinary H2. A quotient onto two copies of a simple module would
therefore require at least twice its commuting-endomorphism dimension.
-/

set_option autoImplicit false
noncomputable section
universe u

namespace Kourovka2135.FrattiniCohomologyMultiplicity

open Representation
open AbelianExtensionCocycle

variable {k Q W V : Type u} [Field k] [Group Q]
variable [AddCommGroup W] [Module k W] [AddCommGroup V] [Module k V]
variable (ρW : Representation k Q W) (ρV : Representation k Q V)

/-- Postcompose each projection of an actual two-copy quotient independently. -/
def twoCopyPostcomposition (f : ρW.IntertwiningMap (ρV.prod ρV)) :
    ((ρV.IntertwiningMap ρV) × (ρV.IntertwiningMap ρV)) →ₗ[k]
      (ρW.IntertwiningMap ρV) where
  toFun a := a.1.comp ((IntertwiningMap.fst k ρV ρV).comp f) +
    a.2.comp ((IntertwiningMap.snd k ρV ρV).comp f)
  map_add' a b := by
    ext w
    change (a.1 (f w).1 + b.1 (f w).1) + (a.2 (f w).2 + b.2 (f w).2) =
      (a.1 (f w).1 + a.2 (f w).2) + (b.1 (f w).1 + b.2 (f w).2)
    abel
  map_smul' a b := by
    ext w
    change a • b.1 (f w).1 + a • b.2 (f w).2 =
      a • (b.1 (f w).1 + b.2 (f w).2)
    exact (smul_add _ _ _).symm

/-- Surjectivity of the actual two-copy map detects both endomorphisms. -/
theorem twoCopyPostcomposition_injective
    (f : ρW.IntertwiningMap (ρV.prod ρV)) (hf : Function.Surjective f) :
    Function.Injective (twoCopyPostcomposition ρW ρV f) := by
  intro a b hab
  have happ (w : W) : a.1 (f w).1 + a.2 (f w).2 =
      b.1 (f w).1 + b.2 (f w).2 :=
    congrArg (fun l : ρW.IntertwiningMap ρV => l w) hab
  apply Prod.ext
  · ext v
    change a.1 v = b.1 v
    obtain ⟨w, hw⟩ := hf (v, 0)
    have h := happ w
    simpa only [hw, map_zero, add_zero] using h
  · ext v
    change a.2 v = b.2 v
    obtain ⟨w, hw⟩ := hf (0, v)
    have h := happ w
    simpa only [hw, map_zero, zero_add] using h

variable [FiniteDimensional k V]

/-- Every genuine two-copy quotient contributes two full endomorphism spaces. -/
theorem two_mul_end_finrank_le_hom_finrank [FiniteDimensional k W]
    (f : ρW.IntertwiningMap (ρV.prod ρV)) (hf : Function.Surjective f) :
    2 * Module.finrank k (ρV.IntertwiningMap ρV) ≤
      Module.finrank k (ρW.IntertwiningMap ρV) := by
  have h := LinearMap.finrank_le_finrank_of_injective
    (twoCopyPostcomposition_injective ρW ρV f hf)
  simpa only [Module.finrank_prod, two_mul] using h

variable {J : Type u} [Group J] [Finite J] [Finite Q]
variable (S : GroupExtension (Multiplicative W) J Q)
variable (hcompat : CompatibleAction S ρW) [ρV.IsIrreducible]

include hcompat in
/-- The proved factor-set injection gives an ordinary ground-field rank bound. -/
theorem hom_finrank_le_H2 (hΦ : S.inl.range ≤ frattini J) :
    Module.finrank k (ρW.IntertwiningMap ρV) ≤
      Module.finrank k (groupCohomology (Rep.of ρV) 2) := by
  let : FiniteDimensional k (groupCohomology (Rep.of ρV) 2) :=
    GroupCohomologyFieldExtension.finiteDimensional_groupCohomology ρV 1
  exact LinearMap.finrank_le_finrank_of_injective
    (transgression_injective S ρV ρW hcompat hΦ)

include hcompat in
/-- The actual Frattini condition rules out a two-copy quotient below its
necessary H2 dimension. No decomposition of the whole kernel is assumed. -/
theorem not_surjective_two_copies [FiniteDimensional k W]
    (hΦ : S.inl.range ≤ frattini J)
    (hH2 : Module.finrank k (groupCohomology (Rep.of ρV) 2) <
      2 * Module.finrank k (ρV.IntertwiningMap ρV))
    (f : ρW.IntertwiningMap (ρV.prod ρV)) : ¬ Function.Surjective f := by
  intro hf
  have htwo := two_mul_end_finrank_le_hom_finrank ρW ρV f hf
  have hhom := hom_finrank_le_H2 ρW ρV S hcompat hΦ
  omega

include hcompat in
/-- In particular, an H2 bound of one endomorphism degree permits at most one
copy in any actual quotient of a Frattini kernel. -/
theorem not_surjective_two_copies_of_H2_le_end [FiniteDimensional k W]
    (hΦ : S.inl.range ≤ frattini J)
    (hH2 : Module.finrank k (groupCohomology (Rep.of ρV) 2) ≤
      Module.finrank k (ρV.IntertwiningMap ρV))
    (f : ρW.IntertwiningMap (ρV.prod ρV)) : ¬ Function.Surjective f := by
  let : Nontrivial ρV.asModule :=
    IsSimpleModule.nontrivial (MonoidAlgebra k Q) ρV.asModule
  let : Nontrivial V := ρV.asModuleEquiv.symm.toEquiv.nontrivial
  have hpos : 0 < Module.finrank k (ρV.IntertwiningMap ρV) := by
    apply Module.finrank_pos_iff_exists_ne_zero.mpr
    refine ⟨IntertwiningMap.id ρV, ?_⟩
    intro heq
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    apply hv
    exact congrArg (fun a : ρV.IntertwiningMap ρV => a v) heq
  exact not_surjective_two_copies ρW ρV S hcompat hΦ (by omega) f

end Kourovka2135.FrattiniCohomologyMultiplicity
