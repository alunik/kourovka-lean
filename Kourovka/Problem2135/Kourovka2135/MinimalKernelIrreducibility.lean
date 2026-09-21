import Kourovka2135.NormalQuotientRepresentation
import Kourovka2135.MinimalKernelStructure

/-! Minimal noncentrality gives irreducibility of the actual conjugation action
on the center quotient, expressed as its invariant-submodule criterion. -/

set_option autoImplicit false
universe u
namespace Kourovka2135
open scoped IsMulCommutative
variable {G : Type u} [Group G]

theorem minimal_centerQuotient_invariant_submodule_eq_bot_or_top
    (N : Subgroup G) [N.Normal]
    (hmin : ∀ M : Subgroup G, M.Normal → M < N → M ≤ Subgroup.center G)
    (p : ℕ) [Fact p.Prime] [IsElementaryAbelian p (N ⧸ Subgroup.center N)]
    (W : Submodule (ZMod p) (Additive (N ⧸ Subgroup.center N)))
    (hW : ∀ g x, x ∈ W → normalQuotientRepresentation N (Subgroup.center N) p g x ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  let q := QuotientGroup.mk' (Subgroup.center N)
  let L : Subgroup N := W.toAddSubgroup.toSubgroup'.comap q
  let M : Subgroup G := L.map N.subtype
  have hnormal : M.Normal := by
    constructor
    rintro _ ⟨x, hx, rfl⟩ g
    refine ⟨MulAut.conjNormal g x, ?_, rfl⟩
    change Additive.ofMul (q (MulAut.conjNormal g x)) ∈ W
    exact hW g (Additive.ofMul (q x)) hx
  have hMN : M ≤ N := Subgroup.map_subtype_le L
  by_cases heq : M = N
  · right
    apply top_le_iff.mp
    intro x _
    obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective (Subgroup.center N) x.toMul
    have hm : (a : G) ∈ M := by rw [heq]; exact a.property
    obtain ⟨b, hb, hba⟩ := hm
    have hba' : b = a := Subtype.ext hba
    subst b
    change Additive.ofMul (q a) ∈ W at hb
    change q a = x.toMul at ha
    change Additive.ofMul x.toMul ∈ W
    rw [← ha]
    exact hb
  · left
    have hMC := hmin M hnormal (lt_of_le_of_ne hMN heq)
    apply bot_unique
    intro x hx
    obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective (Subgroup.center N) x.toMul
    have hla : a ∈ L := by
      change Additive.ofMul (q a) ∈ W
      change q a = x.toMul at ha
      exact ha.symm ▸ hx
    have hac : (a : G) ∈ Subgroup.center G :=
      hMC (Subgroup.mem_map_of_mem N.subtype hla)
    have hacN : a ∈ Subgroup.center N := by
      apply Subgroup.mem_center_iff.mpr
      intro b
      exact Subtype.ext (Subgroup.mem_center_iff.mp hac b)
    have ha1 : q a = 1 := (QuotientGroup.eq_one_iff _).mpr hacN
    change x = 0
    change x.toMul = 1
    exact ha.symm.trans ha1

end Kourovka2135
