import Kourovka2135.CentralDoubleCoverUniqueness

/-! Proper subgroups of a perfect central cover inherit solubility from
proper subgroups of its quotient. A subgroup with full quotient image would
already fill the perfect cover; its remaining kernel is central abelian. -/

set_option autoImplicit false
namespace Kourovka2135.PerfectCentralProperSolvable
open scoped IsMulCommutative

variable {E Q : Type*} [Group E] [Group Q] [Group.IsPerfect E]

theorem proper_image (π : E →* Q) (hc : π.ker ≤ Subgroup.center E)
    (H : Subgroup E) (hH : H < ⊤) : H.map π < ⊤ := by
  apply lt_top_iff_ne_top.mpr
  intro hm
  have hs : H ⊔ π.ker = ⊤ := by
    have he := congrArg (Subgroup.comap π) hm
    simpa only [Subgroup.comap_map_eq, Subgroup.comap_top] using he
  exact hH.ne (CentralDoubleCoverUniqueness.eq_top_of_sup_central H π.ker hs hc)

theorem proper_subgroup_isSolvable (π : E →* Q)
    (hc : π.ker ≤ Subgroup.center E)
    (hsolv : ∀ H : Subgroup Q, H < ⊤ → Group.IsSolvable H)
    (H : Subgroup E) (hH : H < ⊤) : Group.IsSolvable H := by
  let f := π.subgroupMap H
  let : Group.IsSolvable (H.map π) := hsolv _ (proper_image π hc H hH)
  have hk : f.ker ≤ Subgroup.center H := by
    intro x hx
    have hx' : π (x : E) = 1 := congrArg Subtype.val hx
    apply Subgroup.mem_center_iff.mpr
    intro y
    exact Subtype.ext (Subgroup.mem_center_iff.mp (hc hx') (y : E))
  let : IsMulCommutative f.ker := ⟨⟨fun x y =>
    Subtype.ext (Subgroup.mem_center_iff.mp (hk y.property) x)⟩⟩
  exact Group.isSolvable_of_ker_le_range f.ker.subtype f (by
    rw [f.ker.range_subtype])

end Kourovka2135.PerfectCentralProperSolvable
