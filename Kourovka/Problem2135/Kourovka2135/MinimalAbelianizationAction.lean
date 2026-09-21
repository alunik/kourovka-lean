import Kourovka2135.FrattiniModuleAction
import Kourovka2135.MinimalKernelPAction
import Kourovka2135.MinimalKernelAbelianization

/-! A normal p-subgroup contained in the ambient Frattini subgroup centralizes
the abelianization of a nonabelian minimal noncentral normal p-kernel. -/

set_option autoImplicit false
universe u
namespace Kourovka2135
open scoped IsMulCommutative
variable {G : Type u} [Group G]

def centerImageSubmodule (N : Subgroup G) (K : Subgroup N) [K.Normal]
    (p : ℕ) [Fact p.Prime] [IsElementaryAbelian p (N ⧸ K)] :
    Submodule (ZMod p) (Additive (N ⧸ K)) :=
  AddSubgroup.toZModSubmodule p
    (((Subgroup.center N).map (QuotientGroup.mk' K)).toAddSubgroup)

theorem minimal_quotient_invariant_submodule_eq_center_or_top
    (N : Subgroup G) [N.Normal] (K : Subgroup N) [K.Characteristic]
    (hmin : ∀ H : Subgroup G, H.Normal → H < N → H ≤ Subgroup.center G)
    (p : ℕ) [Fact p.Prime] [IsElementaryAbelian p (N ⧸ K)]
    (U : Submodule (ZMod p) (Additive (N ⧸ K)))
    (hWU : centerImageSubmodule N K p ≤ U)
    (hU : ∀ g x, x ∈ U → normalQuotientRepresentation N K p g x ∈ U) :
    U = centerImageSubmodule N K p ∨ U = ⊤ := by
  let q := QuotientGroup.mk' K
  let L : Subgroup N := U.toAddSubgroup.toSubgroup'.comap q
  let H : Subgroup G := L.map N.subtype
  have hnormal : H.Normal := by
    constructor
    rintro _ ⟨x, hx, rfl⟩ g
    refine ⟨MulAut.conjNormal g x, ?_, rfl⟩
    exact hU g (Additive.ofMul (q x)) hx
  have hHN : H ≤ N := Subgroup.map_subtype_le L
  by_cases heq : H = N
  · right
    apply top_le_iff.mp
    intro x _
    obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective K x.toMul
    have hm : (a : G) ∈ H := by rw [heq]; exact a.property
    obtain ⟨b, hb, hba⟩ := hm
    have hba' : b = a := Subtype.ext hba
    subst b
    change Additive.ofMul (q a) ∈ U at hb
    change q a = x.toMul at ha
    change Additive.ofMul x.toMul ∈ U
    rw [← ha]
    exact hb
  · left
    apply le_antisymm ?_ hWU
    have hHC := hmin H hnormal (lt_of_le_of_ne hHN heq)
    intro x hx
    obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective K x.toMul
    have hla : a ∈ L := by
      change Additive.ofMul (q a) ∈ U
      change q a = x.toMul at ha
      exact ha.symm ▸ hx
    have hac : (a : G) ∈ Subgroup.center G :=
      hHC (Subgroup.mem_map_of_mem N.subtype hla)
    have hacN : a ∈ Subgroup.center N := by
      apply Subgroup.mem_center_iff.mpr
      intro b
      exact Subtype.ext (Subgroup.mem_center_iff.mp hac b)
    exact ⟨a, hacN, ha⟩

theorem centerImageSubmodule_fixed
    (N : Subgroup G) [N.Normal] (K : Subgroup N) [K.Characteristic]
    (hZ : (Subgroup.center N).map N.subtype ≤ Subgroup.center G)
    (p : ℕ) [Fact p.Prime] [IsElementaryAbelian p (N ⧸ K)]
    (g : G) (x : Additive (N ⧸ K)) (hx : x ∈ centerImageSubmodule N K p) :
    normalQuotientRepresentation N K p g x = x := by
  obtain ⟨a, ha, heq⟩ := hx
  have hac : (a : G) ∈ Subgroup.center G := hZ (Subgroup.mem_map_of_mem N.subtype ha)
  have hfix : MulAut.conjNormal g a = a := by
    apply Subtype.ext
    change g * (a : G) * g⁻¹ = a
    rw [Subgroup.mem_center_iff.mp hac g]
    simp only [mul_assoc, mul_inv_cancel, mul_one]
  change normalQuotientRepresentation N K p g (Additive.ofMul x.toMul) =
    Additive.ofMul x.toMul
  rw [← heq, normalQuotientRepresentation_apply_mk, hfix]

theorem minimal_abelianization_frattini_pSubgroup_action
    [Finite G] [Group.IsPerfect G]
    {p : ℕ} (hp : p.Prime) (N : Subgroup G) [N.Normal] (hN : IsPGroup p N)
    (hnonabelian : ¬ IsMulCommutative N)
    (hmin : ∀ H : Subgroup G, H.Normal → H < N → H ≤ Subgroup.center G)
    (R : Subgroup G) [R.Normal] (hR : IsPGroup p R) (hRΦ : R ≤ frattini G)
    (r : R) (x : N) :
    QuotientGroup.mk' (commutator N) (MulAut.conjNormal (r : G) x) =
      QuotientGroup.mk' (commutator N) x := by
  let : Fact p.Prime := ⟨hp⟩
  have hnoncentral : ¬ N ≤ Subgroup.center G := by
    intro h
    apply hnonabelian
    apply Subgroup.center_eq_top_iff.mp
    apply top_le_iff.mp
    intro a _
    apply Subgroup.mem_center_iff.mpr
    intro b
    exact Subtype.ext (Subgroup.mem_center_iff.mp (h a.property) b)
  let : IsElementaryAbelian p (N ⧸ commutator N) :=
    minimal_noncentral_abelianization_isElementaryAbelian hp N hN hnoncentral hmin
  let ρ := normalQuotientRepresentation N (commutator N) p
  let W := centerImageSubmodule N (commutator N) p
  have hW := centerImageSubmodule_fixed N (commutator N)
    (minimal_noncentral_center_le N hnonabelian hmin) p
  have hirr := minimal_quotient_invariant_submodule_eq_center_or_top N (commutator N) hmin p
  have hRdiff : ∀ (a : R) y, ρ (a : G) y - y ∈ W := by
    intro a y
    obtain ⟨b, hb⟩ := QuotientGroup.mk'_surjective (commutator N) y.toMul
    have he := minimal_centerQuotient_pSubgroup_action hp N hN hmin R hR a b
    have hc : MulAut.conjNormal (a : G) b * b⁻¹ ∈ Subgroup.center N := by
      apply (QuotientGroup.eq_one_iff _).mp
      change QuotientGroup.mk' (Subgroup.center N) (MulAut.conjNormal (a : G) b * b⁻¹) = 1
      rw [map_mul, map_inv, he, mul_inv_cancel]
    refine ⟨MulAut.conjNormal (a : G) b * b⁻¹, hc, ?_⟩
    change QuotientGroup.mk' (commutator N) b = y.toMul at hb
    change _ = (ρ (a : G) (Additive.ofMul y.toMul) - Additive.ofMul y.toMul).toMul
    rw [← hb]
    simp only [ρ, normalQuotientRepresentation_apply_mk, toMul_sub,
      toMul_ofMul, map_mul, map_inv, div_eq_mul_inv]
  exact frattini_trivial_action_of_simple_quotient
    (M := Additive (N ⧸ commutator N)) ρ W hW hirr R hRΦ hRdiff r
    (Additive.ofMul (QuotientGroup.mk' (commutator N) x))

end Kourovka2135
