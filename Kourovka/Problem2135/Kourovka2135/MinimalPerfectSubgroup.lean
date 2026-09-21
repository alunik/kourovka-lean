import Kourovka2135.MinimalException

/-! Proper perfect subgroups of a smallest exception centralize its p-core. -/

set_option autoImplicit false
universe u
namespace Kourovka2135
variable {G : Type u} [Group G] [Finite G] {w : OuterWord} {p : ℕ}

theorem OrderMinimalException.proper_perfect_coprime_card
    (h : OrderMinimalException w p G) (hp : p.Prime)
    (H : Subgroup G) (hne : H ≠ ⊤) [Group.IsPerfect H] : (Nat.card H).Coprime p := by
  have hlt : Nat.card H < Nat.card G := by
    simpa only [Subgroup.card_top] using
      (Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hne))
  have hcomp := h.smaller H hlt (h.condition.subgroup H)
  rw [w.verbalSubgroup_eq_top_of_isPerfect] at hcomp
  exact coprime_card_of_isPerfect_hasNormalPComplement p hp
    (hcomp.of_equiv hp Subgroup.topEquiv)

theorem OrderMinimalException.proper_perfect_le_centralizer_pCore
    (h : OrderMinimalException w p G) (hp : p.Prime)
    (H : Subgroup G) (hne : H ≠ ⊤) [Group.IsPerfect H] :
    H ≤ Subgroup.centralizer (pCore p G : Set G) := by
  let d := OuterWord.derivedWord w.height
  have hcard := h.proper_perfect_coprime_card hp H hne
  have hd : ProductOrderCondition d p G := by
    intro x hx y hy hxp hyp
    exact h.condition x (w.derivedWord_values_subset w.height le_rfl hx)
      y (w.derivedWord_values_subset w.height le_rfl hy) hxp hyp
  have hv : d.verbalSubgroup H ≤
      (Subgroup.centralizer (pCore p G : Set G)).comap H.subtype := by
    apply (Subgroup.closure_le _).mpr
    intro x hx
    have hxp : ¬ p ∣ orderOf (x : G) := by
      intro hdiv
      have hxdiv : p ∣ Nat.card H := by
        rw [Subgroup.orderOf_coe x] at hdiv
        exact hdiv.trans (orderOf_dvd_natCard x)
      exact (hp.coprime_iff_not_dvd.mp hcard.symm) hxdiv
    have hcomm := hd.derivedValue_centralizes_pSubgroup hp (pCore p G)
      pCore_isPGroup (d.map_mem_values H.subtype hx) hxp
      (by rw [Subgroup.normalizer_eq_top]; trivial)
    exact fun y hy => (hcomm y hy).eq
  rw [d.verbalSubgroup_eq_top_of_isPerfect] at hv
  intro x hx
  exact hv (show (⟨x, hx⟩ : H) ∈ ⊤ from trivial)

end Kourovka2135
