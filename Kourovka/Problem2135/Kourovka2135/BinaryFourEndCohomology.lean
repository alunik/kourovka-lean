import Kourovka2135.BinaryFourIrreducibleCohomology
import Kourovka2135.BinarySLTwoEndCohomology
import Kourovka2135.PerfectRepresentationDimension
import Kourovka2135.RepresentationGroupEquiv

/-! Nontrivial irreducible coefficients over the original finite field have
vanishing H2 for SL2(4). The actual commuting-field dimension excludes the
trivial tensor, and the proved scalar-extension identity descends vanishing. -/

set_option autoImplicit false
noncomputable section
universe u
namespace Kourovka2135.BinaryFourEndCohomology

open MinimalEndMovingRank BinarySLTwoEndCohomology

variable {K : Type u} [Field K] [CharP K 2]
variable {F : Type u} [Field F] [CharP F 2] [Fintype F]
variable {V : Type u} [AddCommGroup V] [Module K V] [Finite V]

/-- Actual nontrivial action suffices; no H1 nonvanishing is required. -/
theorem subsingleton_H2
    [Group.IsPerfect (SLTwo.SL2 F)]
    (ρ : Representation K (SLTwo.SL2 F) V) [ρ.IsIrreducible]
    (hcard : Fintype.card F = 2 ^ 2) (haction : ∃ g, ρ g ≠ 1) :
    Subsingleton (groupCohomology (Rep.of ρ) 2) := by
  have hdim : Module.finrank (EndField ρ) V ≠ 1 := by
    apply PerfectRepresentationDimension.finrank_ne_one_of_nontrivial_action (overEnd ρ)
    obtain ⟨g, hg⟩ := haction
    exact ⟨g, fun h => hg ((overEnd_eq_one_iff ρ g).mp h)⟩
  have hclosed : Module.finrank (ClosedField ρ) (ExtendedCarrier ρ) ≠ 1 := by
    rwa [finrank_extended_coefficient]
  let : Subsingleton (groupCohomology (Rep.of (extended ρ)) 2) :=
    BinaryFourIrreducibleCohomology.subsingleton_H2
      (ClosedField ρ) (parameterEmbedding ρ) (extended ρ) hcard hclosed
  have hz : Module.finrank (ClosedField ρ)
      (groupCohomology (Rep.of (extended ρ)) 2) = 0 :=
    Module.finrank_zero_of_subsingleton
  have hzero : Module.finrank K (groupCohomology (Rep.of ρ) 2) = 0 := by
    rw [finrank_cohomology_eq_closed ρ 1, hz, mul_zero]
  let : FiniteDimensional K (groupCohomology (Rep.of ρ) 2) :=
    finiteDimensional_cohomology ρ 1
  exact Module.finrank_zero_iff.mp hzero

/-- Pullback along the actual quotient isomorphism transports the same H2 vanishing. -/
theorem subsingleton_H2_of_group_equiv
    {H : Type u} [Group H] [Group.IsPerfect H]
    (ρ : Representation K H V) [ρ.IsIrreducible]
    (e : SLTwo.SL2 F ≃* H) (hcard : Fintype.card F = 2 ^ 2)
    (haction : ∃ g, ρ g ≠ 1) :
    Subsingleton (groupCohomology (Rep.of ρ) 2) := by
  let : Group.IsPerfect (SLTwo.SL2 F) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  let : Representation.IsIrreducible (ρ.comp e.toMonoidHom) :=
    RepresentationGroupEquiv.isIrreducible_comp ρ e
  have ha : ∃ g, (ρ.comp e.toMonoidHom) g ≠ 1 := by
    obtain ⟨g, hg⟩ := haction
    refine ⟨e.symm g, ?_⟩
    simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, e.apply_symm_apply] using hg
  let : Subsingleton (groupCohomology (Rep.of (ρ.comp e.toMonoidHom)) 2) :=
    subsingleton_H2 (ρ.comp e.toMonoidHom) hcard ha
  exact (RepresentationGroupEquiv.cohomologyIso ρ e 2).toLinearEquiv.symm.injective.subsingleton

end Kourovka2135.BinaryFourEndCohomology
