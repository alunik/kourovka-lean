import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Algebra.Group.Subgroup.Ker

/-! Explicit words in two elements for finite generating certificates. -/

set_option autoImplicit false
universe u
namespace Kourovka2135
variable {G : Type u} [Group G]

def pairWord (a b : G) : List ℤ → G
  | [] => 1
  | i :: rest => (if i = 1 then a else if i = -1 then a⁻¹ else
      if i = 2 then b else b⁻¹) * pairWord a b rest

theorem pairWord_mem (H : Subgroup G) {a b : G} (ha : a ∈ H) (hb : b ∈ H)
    (word : List ℤ) : pairWord a b word ∈ H := by
  induction word with
  | nil => exact H.one_mem
  | cons i rest ih =>
    apply H.mul_mem _ ih
    split_ifs
    · exact ha
    · exact H.inv_mem ha
    · exact hb
    · exact H.inv_mem hb

theorem closure_pair_eq_top_of_subtype_closure (H : Subgroup G) (a b : H)
    (h : Subgroup.closure ({(a : G), (b : G)} : Set G) = H) :
    Subgroup.closure ({a, b} : Set H) = ⊤ := by
  apply Subgroup.map_injective H.subtype_injective
  rw [MonoidHom.map_closure, Set.image_pair]
  change Subgroup.closure ({(a : G), (b : G)} : Set G) = (⊤ : Subgroup H).map H.subtype
  rw [h]
  simp only [← MonoidHom.range_eq_map, Subgroup.range_subtype]

end Kourovka2135
