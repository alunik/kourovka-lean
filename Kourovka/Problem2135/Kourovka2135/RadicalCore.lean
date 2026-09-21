import Kourovka2135.MinimalException
import Kourovka2135.SolubleRadical

/-! Relating the p-core of a normal soluble subgroup to the ambient p-core. -/

set_option autoImplicit false
universe u
namespace Kourovka2135
variable {G : Type u} [Group G] [Finite G] {p : ℕ}

omit [Finite G] in
theorem map_pCore_normal_subgroup_le (H : Subgroup G) [H.Normal] :
    (pCore p H).map H.subtype ≤ pCore p G := by
  exact le_sSup ⟨inferInstance, pCore_isPGroup.map H.subtype⟩

theorem normal_soluble_le_center_of_pCore_le_center
    (hp : p.Prime) (hcore : pPrimeCore p G = ⊥)
    (hP : pCore p G ≤ Subgroup.center G)
    (H : Subgroup G) [H.Normal] (hH : Group.IsSolvable H) : H ≤ Subgroup.center G := by
  let : Fact p.Prime := ⟨hp⟩
  have hcoreH := pPrimeCore_eq_bot_of_normal_subgroup hp H hcore
  have hmap := map_pCore_normal_subgroup_le (p := p) H
  intro x hx
  have hxcent : (⟨x, hx⟩ : H) ∈ Subgroup.centralizer (pCore p H : Set H) := by
    intro y hy
    apply Subtype.ext
    exact (Subgroup.mem_center_iff.mp
      (hP (hmap (Subgroup.mem_map_of_mem H.subtype hy))) x).symm
  have hxP := Soluble.centralizer_pCore_le_of_pPrimeCore_eq_bot hH p hcoreH hxcent
  exact hP (hmap (Subgroup.mem_map_of_mem H.subtype hxP))

end Kourovka2135
