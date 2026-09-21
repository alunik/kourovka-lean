import Kourovka2135.QuasisimpleCoprimeCommutators
import Kourovka2135.MinimalQuotientOrder
import Kourovka2135.DerivedCentralization
import Kourovka2135.FrobeniusCriterion

/-! Exclusion of the central-radical branch, conditional on the explicitly
stated uniform quasisimple coprime commutator hypothesis. -/

set_option autoImplicit false
universe u
namespace Kourovka2135

/-- In the central-radical branch every p′-element is a single value of
any prescribed outer word. -/
theorem OrderMinimalException.mem_values_of_radical_le_center
    (quasisimple : QuasisimpleCoprimeCommutators.{u})
    {G : Type u} [Group G] [Finite G] {w : OuterWord} {p : ℕ}
    (h : OrderMinimalException w p G) (hp : p.Prime)
    (hc : solubleRadical G ≤ Subgroup.center G)
    (v : OuterWord) {x : G} (hx : ¬ p ∣ orderOf x) : x ∈ v.values G := by
  let : Fact p.Prime := ⟨hp⟩
  let : Group.IsPerfect G := h.isPerfect hp
  let : IsSimpleGroup (G ⧸ solubleRadical G) := h.quotient_radical_isSimple hp
  have hker : IsPGroup p (QuotientGroup.mk' (solubleRadical G)).ker := by
    rw [QuotientGroup.ker_mk', h.radical_eq_pCore hp]
    exact pCore_isPGroup
  exact quasisimple.mem_values_of_central_p_extension
    (h.quotient_radical_not_isMulCommutative hp)
    (QuotientGroup.mk' (solubleRadical G))
    (QuotientGroup.mk'_surjective (solubleRadical G))
    (by simpa only [QuotientGroup.ker_mk'] using hc) hp hker v hx

/-- The exact product-order condition makes every p′-element of every
p-subgroup normalizer centralize that subgroup in the remaining branch. -/
theorem OrderMinimalException.normalizer_centralizes_of_radical_le_center
    (quasisimple : QuasisimpleCoprimeCommutators.{u})
    {G : Type u} [Group G] [Finite G] {w : OuterWord} {p : ℕ}
    (h : OrderMinimalException w p G) (hp : p.Prime)
    (hc : solubleRadical G ≤ Subgroup.center G)
    (P : Subgroup G) (hP : IsPGroup p P) {x : G}
    (hx : ¬ p ∣ orderOf x) (hxn : x ∈ Subgroup.normalizer (P : Set G)) :
    ∀ g ∈ P, Commute g x := by
  have hd : ProductOrderCondition (OuterWord.derivedWord w.height) p G := by
    intro a ha b hb hap hbp
    exact h.condition a (w.derivedWord_values_subset w.height le_rfl ha)
      b (w.derivedWord_values_subset w.height le_rfl hb) hap hbp
  exact hd.derivedValue_centralizes_pSubgroup hp P hP
    (h.mem_values_of_radical_le_center quasisimple hp hc _ hx) hx hxn

/-- A central-radical least exception cannot occur. -/
theorem OrderMinimalException.false_of_radical_le_center
    (quasisimple : QuasisimpleCoprimeCommutators.{u})
    {G : Type u} [Group G] [Finite G] {w : OuterWord} {p : ℕ}
    (h : OrderMinimalException w p G) (hp : p.Prime)
    (hc : solubleRadical G ≤ Subgroup.center G) : False := by
  have hcomp : HasNormalPComplement p G :=
    hasNormalPComplement_of_normalizer_centralization hp (fun P hP x hx hxn =>
      h.normalizer_centralizes_of_radical_le_center quasisimple hp hc P hP hx hxn)
  exact h.failure (hcomp.subgroup hp (w.verbalSubgroup G))

end Kourovka2135
