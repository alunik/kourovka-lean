import Mathlib.RepresentationTheory.Irreducible
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! Irreducibility of the actual finite-dimensional contragredient.

For a subrepresentation of the dual, its common annihilator in the
original space is invariant. Simplicity makes this annihilator either
zero or the whole space; finite-dimensional double annihilation then
recovers the two corresponding possibilities for the dual subspace.
-/

set_option autoImplicit false
noncomputable section
universe u v w

namespace Kourovka2135.RepresentationDualIrreducible

variable {k : Type u} [Field k] {G : Type v} [Group G]
variable {V : Type w} [AddCommGroup V] [Module k V]
variable (ρ : Representation k G V)

/-- The common annihilator of a dual invariant subspace is an actual subrepresentation. -/
def coannihilator (S : Subrepresentation ρ.dual) : Subrepresentation ρ where
  toSubmodule := S.toSubmodule.dualCoannihilator
  apply_mem_toSubmodule g x hx := by
    apply (Submodule.mem_dualCoannihilator _).mpr
    intro ell hell
    have h := (Submodule.mem_dualCoannihilator x).mp hx
      (ρ.dual g⁻¹ ell) (S.apply_mem_toSubmodule g⁻¹ hell)
    change ell (ρ (g⁻¹)⁻¹ x) = 0 at h
    simpa only [inv_inv] using h

@[simp] theorem coannihilator_toSubmodule (S : Subrepresentation ρ.dual) :
    (coannihilator ρ S).toSubmodule = S.toSubmodule.dualCoannihilator := rfl

/-- The genuine contragredient of a finite-dimensional irreducible group representation
is irreducible over the same field. No assumption on the group's order or the characteristic
is required. -/
theorem isIrreducible_dual [FiniteDimensional k V] [ρ.IsIrreducible] :
    ρ.dual.IsIrreducible := by
  let : Nontrivial ρ.asModule := IsSimpleModule.nontrivial (MonoidAlgebra k G) ρ.asModule
  let : Nontrivial V := ρ.asModuleEquiv.symm.toEquiv.nontrivial
  let : Nontrivial (Module.Dual k V) := (Module.nontrivial_dual_iff k).mpr inferInstance
  have hbot : (⊥ : Subrepresentation ρ.dual) ≠ ⊤ := by
    intro h
    obtain ⟨ell, hell⟩ := exists_ne (0 : Module.Dual k V)
    have hmem : ell ∈ (⊥ : Subrepresentation ρ.dual) := by rw [h]; trivial
    change ell = 0 at hmem
    exact hell hmem
  let : Nontrivial (Subrepresentation ρ.dual) := ⟨⟨⊥, ⊤, hbot⟩⟩
  apply IsSimpleOrder.of_forall_eq_top
  intro S hS
  have hrecover : S.toSubmodule.dualCoannihilator.dualAnnihilator = S.toSubmodule :=
    Subspace.dualCoannihilator_dualAnnihilator_eq
  rcases eq_bot_or_eq_top (coannihilator ρ S) with hU | hU
  · have hu := congrArg Subrepresentation.toSubmodule hU
    change S.toSubmodule.dualCoannihilator = ⊥ at hu
    apply Subrepresentation.toSubmodule_injective
    change S.toSubmodule = ⊤
    rw [← hrecover, hu, Submodule.dualAnnihilator_bot]
  · have hu := congrArg Subrepresentation.toSubmodule hU
    change S.toSubmodule.dualCoannihilator = ⊤ at hu
    have hzero : S = ⊥ := by
      apply Subrepresentation.toSubmodule_injective
      change S.toSubmodule = ⊥
      rw [← hrecover, hu, Submodule.dualAnnihilator_top]
    exact False.elim (hS hzero)

end Kourovka2135.RepresentationDualIrreducible
