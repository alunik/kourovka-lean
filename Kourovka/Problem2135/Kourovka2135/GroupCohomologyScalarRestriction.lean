import Kourovka2135.GroupCohomologyFieldExtension
import Mathlib.Algebra.Module.Submodule.RestrictScalars

/-! Restricting the coefficient field multiplies ordinary cohomology
dimensions by the field degree. The comparison uses the actual unchanged
cochain functions and differentials, and the kernel dimension formula.
-/

set_option autoImplicit false
noncomputable section
universe u

namespace Kourovka2135.GroupCohomologyScalarRestriction

open GroupCohomologyFieldExtension

variable (K : Type u) [Field K] {E G V : Type u} [Field E] [Algebra K E]
variable [Group G] [AddCommGroup V] [Module E V] [Module K V] [IsScalarTower K E V]

/-- Restriction changes linearity but not the actual group action. -/
def restrict (ρ : Representation E G V) : Representation K G V where
  toFun g := (ρ g).restrictScalars K
  map_one' := by
    apply LinearMap.ext
    intro v
    exact congrArg (fun l : Module.End E V => l v) ρ.map_one
  map_mul' g h := by
    apply LinearMap.ext
    intro v
    exact congrArg (fun l : Module.End E V => l v) (ρ.map_mul g h)

@[simp] theorem restrict_apply (ρ : Representation E G V) (g : G) (v : V) :
    restrict K ρ g v = ρ g v := rfl

variable [Finite G]

omit [Finite G] in
/-- The cochain differential is the identical function after scalar restriction. -/
theorem differential_restrict (ρ : Representation E G V) (n : ℕ) :
    differential (restrict K ρ) n = (differential ρ n).restrictScalars K := by
  apply LinearMap.ext
  intro v
  funext g
  simp only [differential, inhomogeneousCochains.d_hom_apply,
    LinearMap.restrictScalars_apply, restrict_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [← IsScalarTower.algebraMap_smul E ((-1 : K) ^ (j.val + 1)),
    map_pow, map_neg, map_one]

omit [Finite G] in
/-- Exact scalar-restriction dimension of an actual differential kernel. -/
theorem finrank_ker_differential_restrict (ρ : Representation E G V) (n : ℕ) :
    Module.finrank K (LinearMap.ker (differential (restrict K ρ) n)) =
      Module.finrank K E * Module.finrank E (LinearMap.ker (differential ρ n)) := by
  rw [differential_restrict, LinearMap.ker_restrictScalars]
  calc
    Module.finrank K ((LinearMap.ker (differential ρ n)).restrictScalars K) =
        Module.finrank K (LinearMap.ker (differential ρ n)) :=
      ((Submodule.restrictScalarsEquiv K E ((Fin n → G) → V)
        (LinearMap.ker (differential ρ n))).restrictScalars K).finrank_eq
    _ = _ := (Module.finrank_mul_finrank K E
      (LinearMap.ker (differential ρ n))).symm

variable [FiniteDimensional K E] [FiniteDimensional E V]

/-- Positive-degree ordinary cohomology obeys the exact coefficient-field tower law. -/
theorem finrank_groupCohomology_restrict (ρ : Representation E G V) (n : ℕ) :
    Module.finrank K (groupCohomology (Rep.of (restrict K ρ)) (n + 1)) =
      Module.finrank K E * Module.finrank E (groupCohomology (Rep.of ρ) (n + 1)) := by
  let : FiniteDimensional K V := FiniteDimensional.trans K E V
  have hK := finrank_groupCohomology_add_finrank_cochains (restrict K ρ) n
  have hE := congrArg (fun x : ℕ => Module.finrank K E * x)
    (finrank_groupCohomology_add_finrank_cochains ρ n)
  rw [finrank_ker_differential_restrict, finrank_ker_differential_restrict,
    ← Module.finrank_mul_finrank K E ((Fin n → G) → V)] at hK
  simp only [Nat.mul_add] at hE
  omega

theorem finrank_H1_restrict (ρ : Representation E G V) :
    Module.finrank K (groupCohomology (Rep.of (restrict K ρ)) 1) =
      Module.finrank K E * Module.finrank E (groupCohomology (Rep.of ρ) 1) :=
  finrank_groupCohomology_restrict K ρ 0

theorem finrank_H2_restrict (ρ : Representation E G V) :
    Module.finrank K (groupCohomology (Rep.of (restrict K ρ)) 2) =
      Module.finrank K E * Module.finrank E (groupCohomology (Rep.of ρ) 2) :=
  finrank_groupCohomology_restrict K ρ 1

end Kourovka2135.GroupCohomologyScalarRestriction
