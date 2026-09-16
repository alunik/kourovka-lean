import Kourovka.Problems.P21_38.Proof.Spread
import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# Ordinary generation inside a subgroup

These algebraic bridges identify generation in a subgroup with ordinary closure
in the ambient group, and recover a subgroup from its homomorphic image when it
contains the kernel. They make no assumption about Thompson's group or the
existence of generating companions.
-/

namespace Kourovka.P21_38

variable {G A : Type*} [Group G] [Group A]

/-- A pair generates the subgroup as a group exactly when its ordinary closure
in the ambient group is that subgroup. -/
theorem generatesPair_subgroup_iff (S : Subgroup G) (a b : S) :
    GeneratesPair a b ↔
      Subgroup.closure ({(a : G), (b : G)} : Set G) = S := by
  change Subgroup.closure ({a, b} : Set S) = ⊤ ↔ _
  rw [← Subgroup.map_subtype_inj (H := S)
    (K := Subgroup.closure ({a, b} : Set S)) (L := ⊤)]
  rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  simp

/-- Two subgroups containing the kernel are equal if their images are equal. -/
theorem subgroup_eq_of_ker_le_of_map_eq (π : G →* A) {H S : Subgroup G}
    (hH : π.ker ≤ H) (hS : π.ker ≤ S) (hmap : H.map π = S.map π) :
    H = S := by
  exact Subgroup.map_injective_of_ker_le π hH hS hmap

/-- A subgroup containing the kernel fills an ambient subgroup as soon as
their images under the homomorphism agree. -/
theorem subgroup_eq_of_le_of_ker_le_of_map_eq (π : G →* A) {H S : Subgroup G}
    (hle : H ≤ S) (hker : π.ker ≤ H) (hmap : H.map π = S.map π) :
    H = S := by
  exact subgroup_eq_of_ker_le_of_map_eq π hker (hker.trans hle) hmap

end Kourovka.P21_38
