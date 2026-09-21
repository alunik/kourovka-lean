import Kourovka2135.CocycleGeneratorBounds
import Mathlib.LinearAlgebra.Prod
import Mathlib.Tactic.FinCases

/-! Two torsion relations suffice to bound first cohomology from the ranks of
actual generator norm operators. Generation and the two power identities are
explicit hypotheses; no presentation or cohomology value is assumed. -/

set_option autoImplicit false
noncomputable section
universe u v

namespace Kourovka2135.CocycleTwoPowerNorms

open groupCohomology CocycleGeneratorEvaluation

section Norm
variable {k : Type u} {V : Type v} [Field k] [AddCommGroup V] [Module k V]

def normTwo (A : Module.End k V) : Module.End k V := A + 1

def normFour (A : Module.End k V) : Module.End k V := A ^ 3 + A ^ 2 + A + 1

end Norm

variable {k G V : Type u} [Field k] [Group G] [AddCommGroup V] [Module k V]
variable (ρ : Representation k G V) (C B : G)

def generators : Fin 2 → G := ![C, B]

private theorem two_word (hC : C ^ 2 = 1) :
    wordValue (generators C B) [0, 0] = 1 := by
  simpa only [wordValue, generators, Matrix.cons_val_zero, mul_one, pow_two] using hC

private theorem four_word (hB : B ^ 4 = 1) :
    wordValue (generators C B) [1, 1, 1, 1] = 1 := by
  simpa only [wordValue, generators, Matrix.cons_val_one, Matrix.cons_val_zero,
    mul_one, pow_succ, pow_zero, one_mul, mul_assoc] using hB

include B in
private theorem normTwo_cocycle (hC : C ^ 2 = 1)
    (z : cocycles₁ (Rep.of ρ)) : normTwo (ρ C) (z C) = 0 := by
  have h := wordDerivative_evaluation ρ (generators C B) [0, 0] z
  rw [two_word C B hC, cocycles₁_map_one] at h
  change wordDerivative ρ (generators C B) [0, 0]
    (fun i => z (generators C B i)) = 0 at h
  simpa only [wordDerivative, generators, Matrix.cons_val_zero,
    LinearMap.zero_apply, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, map_zero, add_zero, zero_add, normTwo,
    Module.End.one_apply] using h

include C in
private theorem normFour_cocycle (hB : B ^ 4 = 1)
    (z : cocycles₁ (Rep.of ρ)) : normFour (ρ B) (z B) = 0 := by
  have h := wordDerivative_evaluation ρ (generators C B) [1, 1, 1, 1] z
  rw [four_word C B hB, cocycles₁_map_one] at h
  change wordDerivative ρ (generators C B) [1, 1, 1, 1]
    (fun i => z (generators C B i)) = 0 at h
  simpa only [wordDerivative, generators, Matrix.cons_val_one, Matrix.cons_val_zero,
    LinearMap.zero_apply, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, map_zero, add_zero, zero_add, normFour,
    pow_succ, pow_zero, Module.End.mul_apply, Module.End.one_apply,
    map_add, add_assoc] using h

/-- Actual cocycles inject into the product of the two actual norm kernels. -/
def evaluationKernels (hC : C ^ 2 = 1) (hB : B ^ 4 = 1) :
    cocycles₁ (Rep.of ρ) →ₗ[k]
      (LinearMap.ker (normTwo (ρ C)) × LinearMap.ker (normFour (ρ B))) :=
  (((LinearMap.proj (0 : Fin 2)).comp (evaluation ρ (generators C B))).codRestrict _
    (normTwo_cocycle ρ C B hC)).prod
  (((LinearMap.proj (1 : Fin 2)).comp (evaluation ρ (generators C B))).codRestrict _
    (normFour_cocycle ρ C B hB))

theorem evaluationKernels_injective
    (hgen : Subgroup.closure (Set.range (generators C B)) = ⊤)
    (hC : C ^ 2 = 1) (hB : B ^ 4 = 1) :
    Function.Injective (evaluationKernels ρ C B hC hB) := by
  intro z w h
  apply evaluation_injective ρ (generators C B) hgen
  funext i
  fin_cases i
  · exact congrArg (fun p => p.1.val) h
  · exact congrArg (fun p => p.2.val) h

variable [FiniteDimensional k V]

/-- The sum of the two norm ranks subtracts from the coefficient dimension. -/
theorem finrank_H1_add_norm_ranks_le
    (hgen : Subgroup.closure (Set.range (generators C B)) = ⊤)
    (hC : C ^ 2 = 1) (hB : B ^ 4 = 1)
    (hinv : ρ.invariants = ⊥) :
    Module.finrank k (groupCohomology (Rep.of ρ) 1) +
      Module.finrank k (LinearMap.range (normTwo (ρ C))) +
      Module.finrank k (LinearMap.range (normFour (ρ B))) ≤ Module.finrank k V := by
  let : FiniteDimensional k (cocycles₁ (Rep.of ρ)) :=
    CocycleGeneratorBounds.finiteDimensional_cocycles ρ (generators C B) hgen
  have hz := LinearMap.finrank_le_finrank_of_injective
    (evaluationKernels_injective ρ C B hgen hC hB)
  rw [Module.finrank_prod] at hz
  have hh := CocycleGeneratorBounds.finrank_H1_add_coefficient ρ (generators C B) hgen
  rw [hinv, finrank_bot, add_zero] at hh
  have hc := (normTwo (ρ C)).finrank_range_add_finrank_ker
  have hb := (normFour (ρ B)).finrank_range_add_finrank_ker
  omega

/-- The C2-free and C4-free rank bounds give H1 at most one quarter of the dimension. -/
theorem finrank_H1_le_quarter
    (hgen : Subgroup.closure (Set.range (generators C B)) = ⊤)
    (hC : C ^ 2 = 1) (hB : B ^ 4 = 1)
    (hinv : ρ.invariants = ⊥) (r : ℕ)
    (hdim : Module.finrank k V = 4 * r)
    (hc : 2 * r ≤ Module.finrank k (LinearMap.range (normTwo (ρ C))))
    (hb : r ≤ Module.finrank k (LinearMap.range (normFour (ρ B)))) :
    Module.finrank k (groupCohomology (Rep.of ρ) 1) ≤ r := by
  have h := finrank_H1_add_norm_ranks_le ρ C B hgen hC hB hinv
  rw [hdim] at h
  omega

end Kourovka2135.CocycleTwoPowerNorms
