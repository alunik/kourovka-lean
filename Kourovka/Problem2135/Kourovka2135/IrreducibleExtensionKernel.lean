import Kourovka2135.AbelianExtensionCocycle
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Field.ZMod

/-! An actual irreducible elementary-abelian extension kernel is minimal
normal. The invariant subspace is constructed from the actual preimage
of a normal subgroup, using the extension's compatible conjugation action.
No finiteness, simplicity, or semisimplicity hypothesis on the ambient
group or its group algebra is needed. -/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.IrreducibleExtensionKernel

open AbelianExtensionCocycle

variable (p : ℕ)
variable {J Q W : Type} [Group J] [Group Q]
variable [AddCommGroup W] [Module (ZMod p) W]
variable (S : GroupExtension (Multiplicative W) J Q)
variable (ρ : Representation (ZMod p) Q W)
variable (hcompat : CompatibleAction S ρ)

/-- The actual additive preimage of a normal subgroup is invariant under
the quotient representation because its action is actual conjugation. -/
def normalPreimage (M : Subgroup J) [M.Normal] : Subrepresentation ρ where
  toSubmodule := AddSubgroup.toZModSubmodule p (M.comap S.inl).toAddSubgroup'
  apply_mem_toSubmodule q w hw := by
    obtain ⟨j, rfl⟩ := S.rightHom_surjective q
    change embed S (ρ (S.rightHom j) w) ∈ M
    change embed S w ∈ M at hw
    rw [hcompat j w]
    exact (inferInstance : M.Normal).conj_mem _ hw j

@[simp] theorem mem_normalPreimage (M : Subgroup J) [M.Normal] (w : W) :
    w ∈ normalPreimage p S ρ hcompat M ↔ embed S w ∈ M := Iff.rfl

variable [Fact p.Prime] [ρ.IsIrreducible]

include hcompat in
/-- There is no nontrivial proper normal subgroup of the actual kernel
when its actual quotient representation is irreducible. -/
theorem normal_eq_bot_or_eq_range (M : Subgroup J) [M.Normal]
    (hM : M ≤ S.inl.range) : M = ⊥ ∨ M = S.inl.range := by
  rcases eq_bot_or_eq_top (normalPreimage p S ρ hcompat M) with hz | ht
  · left
    apply bot_unique
    intro j hj
    obtain ⟨w, hw⟩ := hM hj
    have hm : w.toAdd ∈ normalPreimage p S ρ hcompat M := by
      change S.inl w ∈ M
      rw [hw]
      exact hj
    rw [hz] at hm
    have hw1 : w = 1 := hm
    change j = 1
    rw [← hw, hw1, map_one]
  · right
    apply le_antisymm hM
    intro j hj
    obtain ⟨w, rfl⟩ := hj
    have hm : w.toAdd ∈ normalPreimage p S ρ hcompat M := by
      rw [ht]
      trivial
    exact hm

include hcompat in
/-- The nonzero normal-subgroup form of actual kernel minimality. -/
theorem eq_range_of_ne_bot (M : Subgroup J) [M.Normal]
    (hM : M ≤ S.inl.range) (hne : M ≠ ⊥) : M = S.inl.range :=
  (normal_eq_bot_or_eq_range p S ρ hcompat M hM).resolve_left hne

include ρ in
/-- Irreducibility also makes the actual extension kernel nontrivial. -/
theorem range_ne_bot : S.inl.range ≠ ⊥ := by
  let : Nontrivial ρ.asModule :=
    IsSimpleModule.nontrivial (MonoidAlgebra (ZMod p) Q) ρ.asModule
  let : Nontrivial W := ρ.asModuleEquiv.symm.toEquiv.nontrivial
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  intro h
  have hm : embed S w ∈ S.inl.range := ⟨Multiplicative.ofAdd w, rfl⟩
  rw [h] at hm
  have he : embed S w = embed S (0 : W) := by
    simpa only [Subgroup.mem_bot, embed_zero] using hm
  exact hw (embed_injective S he)

end Kourovka2135.IrreducibleExtensionKernel
