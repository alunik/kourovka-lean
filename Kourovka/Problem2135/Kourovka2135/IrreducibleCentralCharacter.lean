import Kourovka2135.CenterSupportedCharacterDegree
import Mathlib.Algebra.Group.Units.Hom
import Mathlib.GroupTheory.Commutator.Basic

/-! The actual unit-valued central character of an irreducible representation.
Scalar Schur's lemma supplies each central scalar; uniqueness makes these
scalars a homomorphism, and a homomorphism from a group automatically has
unit-valued image. No finite-group, characteristic-zero, faithful-action, or
extraspecial-group hypothesis is required. -/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.IrreducibleCentralCharacter

open Representation
open scoped MonoidAlgebra

variable {k G V : Type*} [Field k] [IsAlgClosed k] [Group G]
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]
variable (ρ : Representation k G V) [ρ.IsIrreducible]

/-- The scalar of the actual action of a central element. -/
def scalar (z : Subgroup.center G) : k :=
  Classical.choose
    (CenterSupportedCharacterDegree.center_apply_eq_smul_id_of_irreducible ρ z.property)

theorem scalar_spec (z : Subgroup.center G) :
    ρ (z : G) = scalar ρ z • (1 : Module.End k V) :=
  Classical.choose_spec
    (CenterSupportedCharacterDegree.center_apply_eq_smul_id_of_irreducible ρ z.property)

/-- Irreducibility rules out the zero coefficient space, so a central scalar is unique. -/
theorem scalar_unique (z : Subgroup.center G) (a : k)
    (ha : ρ (z : G) = a • (1 : Module.End k V)) : scalar ρ z = a := by
  let : Nontrivial ρ.asModule := IsSimpleModule.nontrivial k[G] ρ.asModule
  let : Nontrivial V := ρ.asModuleEquiv.symm.toEquiv.nontrivial
  apply smul_left_injective k (one_ne_zero : (1 : Module.End k V) ≠ 0)
  exact (scalar_spec ρ z).symm.trans ha

/-- Multiplication of the actual operators makes the chosen scalars multiplicative. -/
def scalarHom : Subgroup.center G →* k where
  toFun := scalar ρ
  map_one' := scalar_unique ρ 1 1 (by simp)
  map_mul' z w := scalar_unique ρ (z * w) (scalar ρ z * scalar ρ w) (by
    change ρ ((z : G) * (w : G)) = _
    rw [map_mul, scalar_spec, scalar_spec]
    simp only [mul_smul_comm, mul_one, smul_smul]
    rw [mul_comm])

/-- The unit-valued central character is constructed from the actual action. -/
def centralCharacter : Subgroup.center G →* kˣ := (scalarHom ρ).toHomUnits

@[simp] theorem centralCharacter_val (z : Subgroup.center G) :
    (centralCharacter ρ z : k) = scalar ρ z := rfl

/-- Exact scalar evaluation of the original representation. -/
theorem centralCharacter_spec (z : Subgroup.center G) :
    ρ (z : G) = (centralCharacter ρ z : k) • (1 : Module.End k V) :=
  scalar_spec ρ z

/-- Exact scalar action on every coefficient vector. -/
theorem centralCharacter_apply (z : Subgroup.center G) (v : V) :
    ρ (z : G) v = (centralCharacter ρ z : k) • v := by
  rw [centralCharacter_spec]
  rfl

/-- The ordinary character on the center is the degree times its central character. -/
theorem character_center (z : Subgroup.center G) :
    ρ.character (z : G) = (Module.finrank k V : k) * (centralCharacter ρ z : k) := by
  change LinearMap.trace k V (ρ (z : G)) = _
  rw [centralCharacter_spec, map_smul, LinearMap.trace_one, smul_eq_mul, mul_comm]

/-- The central character detects exactly the central elements acting trivially. -/
theorem centralCharacter_eq_one_iff (z : Subgroup.center G) :
    centralCharacter ρ z = 1 ↔ ρ (z : G) = 1 := by
  constructor
  · intro hz
    rw [centralCharacter_spec, hz, Units.val_one, one_smul]
  · intro hz
    apply Units.ext
    change scalar ρ z = 1
    apply scalar_unique ρ z 1
    simpa only [one_smul] using hz

/-- Nontrivial action on any central subgroup gives a nontrivial central character there. -/
theorem exists_centralCharacter_ne_one
    (D : Subgroup G) (hDZ : D ≤ Subgroup.center G)
    (hD : ∃ d : D, ρ (d : G) ≠ 1) :
    ∃ d : D, centralCharacter ρ (Subgroup.inclusion hDZ d) ≠ 1 := by
  obtain ⟨d, hd⟩ := hD
  refine ⟨d, ?_⟩
  intro h
  exact hd ((centralCharacter_eq_one_iff ρ (Subgroup.inclusion hDZ d)).mp h)

/-- In particular, the derived-action premise gives a nontrivial restriction to the derived group. -/
theorem derived_restriction_ne_one
    (hDZ : commutator G ≤ Subgroup.center G)
    (hD : ∃ d : commutator G, ρ (d : G) ≠ 1) :
    (centralCharacter ρ).comp (Subgroup.inclusion hDZ) ≠ 1 := by
  obtain ⟨d, hd⟩ := exists_centralCharacter_ne_one ρ (commutator G) hDZ hD
  intro h
  apply hd
  exact congrArg (fun f : commutator G →* kˣ => f d) h

end Kourovka2135.IrreducibleCentralCharacter
