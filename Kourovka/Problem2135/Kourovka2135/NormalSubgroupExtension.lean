import Mathlib.GroupTheory.GroupExtension.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! The actual short exact sequence associated to a normal subgroup, with
its kernel written additively for use by the factor-set constructions.
-/

set_option autoImplicit false
universe u
namespace Kourovka2135.NormalSubgroupExtension

variable {G : Type u} [Group G] (N : Subgroup G) [N.Normal]

/-- The normal subgroup's inclusion, with only notation on its source changed. -/
def inclusion : Multiplicative (Additive N) →* G where
  toFun n := n.toAdd.toMul.val
  map_one' := rfl
  map_mul' _ _ := rfl

omit [N.Normal] in
@[simp] theorem inclusion_apply (n : N) :
    inclusion N (Multiplicative.ofAdd (Additive.ofMul n)) = (n : G) := rfl

omit [N.Normal] in
theorem inclusion_injective : Function.Injective (inclusion N) := by
  intro a b h
  exact Subtype.ext h

omit [N.Normal] in
theorem inclusion_range : (inclusion N).range = N := by
  ext g
  constructor
  · rintro ⟨n, rfl⟩
    exact n.toAdd.toMul.property
  · intro hg
    exact ⟨Multiplicative.ofAdd (Additive.ofMul ⟨g, hg⟩), rfl⟩

/-- The actual kernel inclusion and quotient map form a group extension. -/
def extension : GroupExtension (Multiplicative (Additive N)) G (G ⧸ N) where
  inl := inclusion N
  rightHom := QuotientGroup.mk' N
  inl_injective := inclusion_injective N
  range_inl_eq_ker_rightHom := by rw [inclusion_range, QuotientGroup.ker_mk']
  rightHom_surjective := QuotientGroup.mk'_surjective N

@[simp] theorem extension_inl_range : (extension N).inl.range = N :=
  inclusion_range N

@[simp] theorem extension_rightHom (g : G) :
    (extension N).rightHom g = QuotientGroup.mk' N g := rfl

end Kourovka2135.NormalSubgroupExtension
