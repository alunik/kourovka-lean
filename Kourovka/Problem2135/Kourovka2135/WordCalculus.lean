import Kourovka2135.OuterWord
import Mathlib.Algebra.Group.Commute.Basic
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Word calculus for the soluble reduction

This module connects the single-value tree model to subgroup commutators.
The convention difference is handled explicitly: the paper's `[a,b]` is
mathlib's commutator of `a⁻¹` and `b⁻¹`.
-/

set_option autoImplicit false

universe u

namespace Kourovka2135.OuterWord

open scoped commutatorElement

variable {G : Type u} [Group G]

/-- The verbal subgroup of a bracket is the commutator of the two verbal
subgroups. This statement concerns generated subgroups, not multiplication
closure of the sets of single values. -/
theorem verbalSubgroup_bracket (left right : OuterWord) :
    (bracket left right).verbalSubgroup G =
      ⁅left.verbalSubgroup G, right.verbalSubgroup G⁆ := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := (mem_values_bracket left right x).mp hx
    have ha' := (left.verbalSubgroup G).inv_mem (left.mem_verbalSubgroup_of_mem_values ha)
    have hb' := (right.verbalSubgroup G).inv_mem (right.mem_verbalSubgroup_of_mem_values hb)
    change a⁻¹ * b⁻¹ * a * b ∈ ⁅left.verbalSubgroup G, right.verbalSubgroup G⁆
    simpa only [commutatorElement_def, inv_inv] using
      Subgroup.commutator_mem_commutator ha' hb'
  · let N := (bracket left right).verbalSubgroup G
    let f : G →* G ⧸ N := QuotientGroup.mk' N
    have hbase (a : G) (ha : a ∈ left.values G) (b : G) (hb : b ∈ right.values G) :
        Commute (f a) (f b) := by
      apply commutatorElement_eq_one_iff_commute.mp
      rw [← map_commutatorElement]
      apply (QuotientGroup.eq_one_iff _).mpr
      apply (bracket left right).mem_verbalSubgroup_of_mem_values
      exact (mem_values_bracket left right _).mpr
        ⟨a⁻¹, left.inv_mem_values ha, b⁻¹, right.inv_mem_values hb,
          by simp only [commutatorElement_def, inv_inv]⟩
    have hcomm (a : G) (ha : a ∈ left.verbalSubgroup G)
        (b : G) (hb : b ∈ right.verbalSubgroup G) : Commute (f a) (f b) := by
      induction ha using Subgroup.closure_induction with
      | mem a ha =>
          induction hb using Subgroup.closure_induction with
          | mem b hb => exact hbase a ha b hb
          | one => simp
          | mul b c _ _ ihb ihc => simpa only [map_mul] using ihb.mul_right ihc
          | inv b _ ih => simpa only [map_inv] using (Commute.inv_right ih)
      | one => simp
      | mul a c _ _ iha ihc => simpa only [map_mul] using iha.mul_left ihc
      | inv a _ ih => simpa only [map_inv] using (Commute.inv_left ih)
    apply Subgroup.commutator_le.mpr
    intro a ha b hb
    apply (QuotientGroup.eq_one_iff _).mp
    change f ⁅a, b⁆ = 1
    rw [map_commutatorElement]
    exact (hcomm a ha b hb).commutator_eq

theorem verbalSubgroup_bracket_le_left (left right : OuterWord) :
    (bracket left right).verbalSubgroup G ≤ left.verbalSubgroup G := by
  rw [verbalSubgroup_bracket]
  exact Subgroup.commutator_le_left _ _

theorem verbalSubgroup_bracket_le_right (left right : OuterWord) :
    (bracket left right).verbalSubgroup G ≤ right.verbalSubgroup G := by
  rw [verbalSubgroup_bracket]
  exact Subgroup.commutator_le_right _ _

/-- A constituent is a subtree, including the whole tree. -/
inductive Constituent : OuterWord → OuterWord → Prop where
  | refl (w : OuterWord) : Constituent w w
  | left {s l r : OuterWord} : Constituent s l → Constituent s (bracket l r)
  | right {s l r : OuterWord} : Constituent s r → Constituent s (bracket l r)

theorem verbalSubgroup_le_of_constituent {s w : OuterWord} (h : Constituent s w) :
    w.verbalSubgroup G ≤ s.verbalSubgroup G := by
  induction h with
  | refl => exact le_rfl
  | left h ih => exact (verbalSubgroup_bracket_le_left _ _).trans ih
  | right h ih => exact (verbalSubgroup_bracket_le_right _ _).trans ih

/-- `Refines v w` means v is obtained by replacing leaves of w by arbitrary
outer words. Leaf replacements have independent inputs. -/
inductive Refines : OuterWord → OuterWord → Prop where
  | leaf (v : OuterWord) : Refines v leaf
  | bracket {v₁ v₂ w₁ w₂ : OuterWord} :
      Refines v₁ w₁ → Refines v₂ w₂ → Refines (bracket v₁ v₂) (bracket w₁ w₂)

theorem Refines.refl (w : OuterWord) : Refines w w := by
  induction w with
  | leaf => exact .leaf _
  | bracket l r ihl ihr => exact .bracket ihl ihr

theorem Refines.values_subset {v w : OuterWord} (h : Refines v w) :
    v.values G ⊆ w.values G := by
  induction h with
  | leaf => simp
  | bracket hl hr ihl ihr =>
      intro x hx
      obtain ⟨a, ha, b, hb, hab⟩ := (mem_values_bracket _ _ x).mp hx
      exact (mem_values_bracket _ _ x).mpr ⟨a, ihl ha, b, ihr hb, hab⟩

theorem Refines.verbalSubgroup_le {v w : OuterWord} (h : Refines v w) :
    v.verbalSubgroup G ≤ w.verbalSubgroup G :=
  Subgroup.closure_mono h.values_subset

/-- Swapping the root branches does not change the set of single values. -/
theorem values_bracket_swap (left right : OuterWord) :
    (bracket left right).values G = (bracket right left).values G := by
  have inclusion (l r : OuterWord) : (bracket l r).values G ⊆ (bracket r l).values G := by
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := (mem_values_bracket l r x).mp hx
    have hval : b⁻¹ * a⁻¹ * b * a ∈ (bracket r l).values G :=
      (mem_values_bracket r l _).mpr ⟨b, hb, a, ha, rfl⟩
    simpa only [mul_inv_rev, inv_inv, mul_assoc] using (bracket r l).inv_mem_values hval
  exact Set.Subset.antisymm (inclusion left right) (inclusion right left)

end Kourovka2135.OuterWord
