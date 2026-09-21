import Kourovka2135.BinarySLTwoEndCohomology
import Kourovka2135.RepresentationGroupEquiv

/-! Low-degree binary SL2 bounds for an actual isomorphic quotient group.

The group isomorphism pulls back the actual representation on the same
coefficient module. Only the ground-field dimension of its actual commuting
endomorphisms is compared; no equality of endomorphism-field scalar
structures is required.
-/

set_option autoImplicit false
noncomputable section
universe u

namespace Kourovka2135.BinarySLTwoGroupEquivCohomology

open RepresentationGroupEquiv

variable {K : Type u} [Field K]
variable {F : Type u} [Field F] [Fintype F]
variable {H : Type u} [Group H]
variable {V : Type u} [AddCommGroup V] [Module K V] [Finite V]
variable (ρ : Representation K H V) (e : SLTwo.SL2 F ≃* H)

include e

/-- Actual cohomology remains finite-dimensional under the group isomorphism. -/
theorem finiteDimensional_cohomology (n : ℕ) :
    FiniteDimensional K (groupCohomology (Rep.of ρ) (n + 1)) := by
  have : FiniteDimensional K
      (groupCohomology (Rep.of (ρ.comp e.toMonoidHom)) (n + 1)) :=
    BinarySLTwoEndCohomology.finiteDimensional_cohomology (ρ.comp e.toMonoidHom) n
  exact FiniteDimensional.of_injective (cohomologyIso ρ e (n + 1)).inv.hom
    (cohomologyIso ρ e (n + 1)).toLinearEquiv.symm.injective

/-- Genuine nontrivial H1 has nonzero dimension because finite-dimensionality is proved. -/
theorem finrank_H1_ne_zero_of_nontrivial
    [Nontrivial (groupCohomology (Rep.of ρ) 1)] :
    Module.finrank K (groupCohomology (Rep.of ρ) 1) ≠ 0 := by
  have : FiniteDimensional K (groupCohomology (Rep.of ρ) 1) :=
    finiteDimensional_cohomology ρ e 0
  exact (Module.finrank_pos (R := K) (M := groupCohomology (Rep.of ρ) 1)).ne'

variable [CharP K 2] [CharP F 2] [ρ.IsIrreducible]

/-- The actual H1 dimension is bounded by the actual commuting-algebra degree. -/
theorem finrank_H1_le_endDegree (f : ℕ) (hcard : Fintype.card F = 2 ^ f) (hf : 2 ≤ f) :
    Module.finrank K (groupCohomology (Rep.of ρ) 1) ≤
      Module.finrank K (ρ.IntertwiningMap ρ) := by
  let : Representation.IsIrreducible (ρ.comp e.toMonoidHom) := isIrreducible_comp ρ e
  have h := BinarySLTwoEndCohomology.finrank_H1_le_endDegree
    (ρ.comp e.toMonoidHom) f hcard hf
  change Module.finrank K (groupCohomology (Rep.of (ρ.comp e.toMonoidHom)) 1) ≤
    Module.finrank K (Representation.IntertwiningMap (ρ.comp e.toMonoidHom) (ρ.comp e.toMonoidHom)) at h
  rwa [finrank_cohomology_comp ρ e 1, finrank_endomorphism_comp ρ e] at h

/-- Nonzero H1 forces the coefficient dimension to be twice the actual commuting degree. -/
theorem finrank_coefficient_eq_two_mul_endDegree_of_finrank_H1_ne_zero
    (f : ℕ) (hcard : Fintype.card F = 2 ^ f) (hf : 2 ≤ f)
    (hH : Module.finrank K (groupCohomology (Rep.of ρ) 1) ≠ 0) :
    Module.finrank K V = 2 * Module.finrank K (ρ.IntertwiningMap ρ) := by
  let : Representation.IsIrreducible (ρ.comp e.toMonoidHom) := isIrreducible_comp ρ e
  have hH' : Module.finrank K
      (groupCohomology (Rep.of (ρ.comp e.toMonoidHom)) 1) ≠ 0 := by
    rwa [finrank_cohomology_comp ρ e 1]
  have h := BinarySLTwoEndCohomology.finrank_coefficient_eq_two_mul_endDegree_of_finrank_H1_ne_zero
    (ρ.comp e.toMonoidHom) f hcard hf hH'
  change Module.finrank K V = 2 *
    Module.finrank K (Representation.IntertwiningMap (ρ.comp e.toMonoidHom) (ρ.comp e.toMonoidHom)) at h
  rwa [finrank_endomorphism_comp ρ e] at h

/-- The dimension dichotomy also accepts actual nontriviality of H1. -/
theorem finrank_coefficient_eq_two_mul_endDegree_of_H1_nontrivial
    (f : ℕ) (hcard : Fintype.card F = 2 ^ f) (hf : 2 ≤ f)
    [Nontrivial (groupCohomology (Rep.of ρ) 1)] :
    Module.finrank K V = 2 * Module.finrank K (ρ.IntertwiningMap ρ) :=
  finrank_coefficient_eq_two_mul_endDegree_of_finrank_H1_ne_zero ρ e f hcard hf
    (finrank_H1_ne_zero_of_nontrivial ρ e)

/-- Numerical H1 vanishing outside the actual ground-field dimension exception. -/
theorem finrank_H1_eq_zero_of_coefficient_ne_two_mul_endDegree
    (f : ℕ) (hcard : Fintype.card F = 2 ^ f) (hf : 2 ≤ f)
    (hdim : Module.finrank K V ≠ 2 * Module.finrank K (ρ.IntertwiningMap ρ)) :
    Module.finrank K (groupCohomology (Rep.of ρ) 1) = 0 := by
  by_contra hH
  exact hdim
    (finrank_coefficient_eq_two_mul_endDegree_of_finrank_H1_ne_zero ρ e f hcard hf hH)

/-- This is genuine H1 vanishing, with no unproved comparison or classification premise. -/
theorem subsingleton_H1_of_coefficient_ne_two_mul_endDegree
    (f : ℕ) (hcard : Fintype.card F = 2 ^ f) (hf : 2 ≤ f)
    (hdim : Module.finrank K V ≠ 2 * Module.finrank K (ρ.IntertwiningMap ρ)) :
    Subsingleton (groupCohomology (Rep.of ρ) 1) := by
  have : FiniteDimensional K (groupCohomology (Rep.of ρ) 1) :=
    finiteDimensional_cohomology ρ e 0
  exact (Module.finrank_zero_iff (R := K)).mp
    (finrank_H1_eq_zero_of_coefficient_ne_two_mul_endDegree ρ e f hcard hf hdim)

/-- In the nonzero-H1 case, H2 has the same commuting-degree bound for f ≥ 3. -/
theorem finrank_H2_le_endDegree_of_finrank_H1_ne_zero
    (f : ℕ) (hcard : Fintype.card F = 2 ^ f) (hf : 3 ≤ f)
    (hH : Module.finrank K (groupCohomology (Rep.of ρ) 1) ≠ 0) :
    Module.finrank K (groupCohomology (Rep.of ρ) 2) ≤
      Module.finrank K (ρ.IntertwiningMap ρ) := by
  let : Representation.IsIrreducible (ρ.comp e.toMonoidHom) := isIrreducible_comp ρ e
  have hH' : Module.finrank K
      (groupCohomology (Rep.of (ρ.comp e.toMonoidHom)) 1) ≠ 0 := by
    rwa [finrank_cohomology_comp ρ e 1]
  have h := BinarySLTwoEndCohomology.finrank_H2_le_endDegree_of_finrank_H1_ne_zero
    (ρ.comp e.toMonoidHom) f hcard hf hH'
  change Module.finrank K (groupCohomology (Rep.of (ρ.comp e.toMonoidHom)) 2) ≤
    Module.finrank K (Representation.IntertwiningMap (ρ.comp e.toMonoidHom) (ρ.comp e.toMonoidHom)) at h
  rwa [finrank_cohomology_comp ρ e 2, finrank_endomorphism_comp ρ e] at h

/-- The H2 degree bound with actual H1 nontriviality as input. -/
theorem finrank_H2_le_endDegree_of_H1_nontrivial
    (f : ℕ) (hcard : Fintype.card F = 2 ^ f) (hf : 3 ≤ f)
    [Nontrivial (groupCohomology (Rep.of ρ) 1)] :
    Module.finrank K (groupCohomology (Rep.of ρ) 2) ≤
      Module.finrank K (ρ.IntertwiningMap ρ) :=
  finrank_H2_le_endDegree_of_finrank_H1_ne_zero ρ e f hcard hf
    (finrank_H1_ne_zero_of_nontrivial ρ e)

/-- Four-parameter H2 vanishing transports through the actual group isomorphism. -/
theorem finrank_H2_eq_zero_of_finrank_H1_ne_zero_at_two
    (hcard : Fintype.card F = 2 ^ 2)
    (hH : Module.finrank K (groupCohomology (Rep.of ρ) 1) ≠ 0) :
    Module.finrank K (groupCohomology (Rep.of ρ) 2) = 0 := by
  let : Representation.IsIrreducible (ρ.comp e.toMonoidHom) := isIrreducible_comp ρ e
  have hH' : Module.finrank K
      (groupCohomology (Rep.of (ρ.comp e.toMonoidHom)) 1) ≠ 0 := by
    rwa [finrank_cohomology_comp ρ e 1]
  have h := BinarySLTwoEndCohomology.finrank_H2_eq_zero_of_finrank_H1_ne_zero_at_two
    (ρ.comp e.toMonoidHom) hcard hH'
  rwa [finrank_cohomology_comp ρ e 2] at h

/-- Genuine H2 vanishing over four parameters under numerical H1 nonvanishing. -/
theorem subsingleton_H2_of_finrank_H1_ne_zero_at_two
    (hcard : Fintype.card F = 2 ^ 2)
    (hH : Module.finrank K (groupCohomology (Rep.of ρ) 1) ≠ 0) :
    Subsingleton (groupCohomology (Rep.of ρ) 2) := by
  have : FiniteDimensional K (groupCohomology (Rep.of ρ) 2) :=
    finiteDimensional_cohomology ρ e 1
  exact (Module.finrank_zero_iff (R := K)).mp
    (finrank_H2_eq_zero_of_finrank_H1_ne_zero_at_two ρ e hcard hH)

/-- Genuine H2 vanishing over four parameters under actual H1 nontriviality. -/
theorem subsingleton_H2_of_H1_nontrivial_at_two
    (hcard : Fintype.card F = 2 ^ 2) [Nontrivial (groupCohomology (Rep.of ρ) 1)] :
    Subsingleton (groupCohomology (Rep.of ρ) 2) :=
  subsingleton_H2_of_finrank_H1_ne_zero_at_two ρ e hcard
    (finrank_H1_ne_zero_of_nontrivial ρ e)

end Kourovka2135.BinarySLTwoGroupEquivCohomology
