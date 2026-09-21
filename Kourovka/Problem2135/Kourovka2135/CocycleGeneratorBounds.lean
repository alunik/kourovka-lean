import Kourovka2135.CocycleGeneratorEvaluation
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Actual H1 dimension bounds from generator values and necessary relations.
Coboundaries are accounted for through the actual low-degree cohomology map.
No presentation, character table, or cohomology value is assumed. -/

set_option autoImplicit false
noncomputable section
universe u v w x

namespace Kourovka2135.CocycleGeneratorBounds

open groupCohomology CategoryTheory CocycleGeneratorEvaluation

variable {k G V : Type u} {I : Type w} {J : Type x} [Field k] [Group G]
variable [AddCommGroup V] [Module k V]
variable (ρ : Representation k G V)

/-- The actual principal one-cocycle associated to a coefficient vector. -/
def principal : V →ₗ[k] cocycles₁ (Rep.of ρ) :=
  (d₀₁ (Rep.of ρ)).hom.codRestrict _ (d₀₁_apply_mem_cocycles₁ (A := Rep.of ρ))

theorem principal_ker : LinearMap.ker (principal ρ) = ρ.invariants := by
  rw [principal, LinearMap.ker_codRestrict, d₀₁_ker_eq_invariants]

/-- The kernel of the actual cohomology projection is precisely the principal range. -/
theorem cohomology_projection_ker :
    LinearMap.ker (H1π (Rep.of ρ)).hom = LinearMap.range (principal ρ) := by
  ext z
  rw [LinearMap.mem_ker, H1π_eq_zero_iff]
  change (z : G → V) ∈ LinearMap.range (d₀₁ (Rep.of ρ)).hom ↔
    z ∈ LinearMap.range (principal ρ)
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, Subtype.ext hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, congrArg Subtype.val hx⟩

variable [Fintype I] [FiniteDimensional k V]
variable (gens : I → G) (hgen : Subgroup.closure (Set.range gens) = ⊤)

include hgen in
/-- Finite generation makes the actual cocycle space finite-dimensional. -/
theorem finiteDimensional_cocycles : FiniteDimensional k (cocycles₁ (Rep.of ρ)) :=
  FiniteDimensional.of_injective (evaluation ρ gens) (evaluation_injective ρ gens hgen)

include hgen in
/-- Rank-nullity in the actual cocycle/coboundary sequence. -/
theorem finrank_H1_add_coefficient :
    Module.finrank k (groupCohomology (Rep.of ρ) 1) + Module.finrank k V =
      Module.finrank k (cocycles₁ (Rep.of ρ)) + Module.finrank k ρ.invariants := by
  let : FiniteDimensional k (cocycles₁ (Rep.of ρ)) := finiteDimensional_cocycles ρ gens hgen
  have hsurj : Function.Surjective (H1π (Rep.of ρ)) :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  have hπ := (H1π (Rep.of ρ)).hom.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, cohomology_projection_ker] at hπ
  change Module.finrank k (groupCohomology (Rep.of ρ) 1) +
    Module.finrank k (LinearMap.range (principal ρ)) =
      Module.finrank k (cocycles₁ (Rep.of ρ)) at hπ
  have hB := (principal ρ).finrank_range_add_finrank_ker
  rw [principal_ker] at hB
  omega

include hgen in
/-- A certified necessary-relation matrix gives a bound for the actual ordinary H1. -/
theorem finrank_H1_constraint_bound (words : J → List I)
    (hwords : ∀ j, wordValue gens (words j) = 1) :
    Module.finrank k (groupCohomology (Rep.of ρ) 1) +
      Module.finrank k (LinearMap.range (constraints ρ gens words)) + Module.finrank k V ≤
        Fintype.card I * Module.finrank k V + Module.finrank k ρ.invariants := by
  have hdim := finrank_H1_add_coefficient ρ gens hgen
  have hZ := finrank_cocycles_le_kernel ρ gens hgen words hwords
  have hT := (constraints ρ gens words).finrank_range_add_finrank_ker
  rw [Module.finrank_pi_fintype] at hT
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at hT
  omega

end Kourovka2135.CocycleGeneratorBounds

namespace Kourovka2135.CocycleGeneratorBounds

open CocycleGeneratorEvaluation

/-- The form used by the two-generator PSL3(3) finite rank certificates. -/
theorem finrank_H1_le_of_two_generator_constraints
    {k G V : Type u} {J : Type x} [Field k] [Group G] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V]
    (ρ : Representation k G V) (gens : Fin 2 → G)
    (hgen : Subgroup.closure (Set.range gens) = ⊤)
    (hinv : ρ.invariants = ⊥)
    (words : J → List (Fin 2)) (hwords : ∀ j, wordValue gens (words j) = 1)
    (c : ℕ) (hrank : Module.finrank k V ≤
      Module.finrank k (LinearMap.range (constraints ρ gens words)) + c) :
    Module.finrank k (groupCohomology (Rep.of ρ) 1) ≤ c := by
  have h := finrank_H1_constraint_bound ρ gens hgen words hwords
  rw [Fintype.card_fin, hinv, finrank_bot, add_zero] at h
  omega

end Kourovka2135.CocycleGeneratorBounds
