import Kourovka2135.OuterCentralization
import Kourovka2135.WordExtensions
import Kourovka2135.NormalComplementCore
import Kourovka2135.PrimeToPValues
import Kourovka2135.SolubleDerived

/-!
# Kourovka 21.35 for arbitrary outer words in finite soluble groups

The induction measure is the word's vertex defect. After passing to the quotient
by the p′-core, every proper same-height extension has a p-group verbal subgroup
by the induction hypothesis. The section bound and conditional centralization
then kill the prime-to-p single values. Soluble focal generation and the verbal
quotient kernel supply the required normal complement.
-/

set_option autoImplicit false
universe u

namespace Kourovka2135

open scoped commutatorElement

/-- In the core-free soluble case, the proper-extension bound and conditional
centralization force every prime-to-p single value of a non-derived word to be
trivial. The same ordered-tree extension family is used in both branch cases. -/
theorem ProductOrderCondition.outerValue_eq_one_of_properExtensions_le_pCore
    {G : Type u} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) (hsolv : Group.IsSolvable G) {α β : OuterWord}
    (h : ProductOrderCondition (OuterWord.bracket α β) p G)
    (hcore : pPrimeCore p G = ⊥)
    (hne : OuterWord.bracket α β ≠
      OuterWord.derivedWord (OuterWord.bracket α β).height)
    (hext : OuterWord.properExtensionSubgroup (OuterWord.bracket α β) G ≤ pCore p G)
    {x : G} (hx : x ∈ (OuterWord.bracket α β).values G)
    (hxp : ¬ p ∣ orderOf x) : x = 1 := by
  let : Fact p.Prime := ⟨hp⟩
  let P := pCore p G
  obtain ⟨i, _, _, hbranch, hbound⟩ :=
    OuterWord.exists_derived_extension_bound (G := G) α β hne
  have hxW : x ∈ (OuterWord.bracket α β).verbalSubgroup G :=
    (OuterWord.bracket α β).mem_verbalSubgroup_of_mem_values hx
  have hxr : ∀ a ∈ (OuterWord.derivedWord i).verbalSubgroup G,
      paperCommutator x a ∈ P := by
    intro a ha
    apply hbound.trans hext
    have hxi := ((OuterWord.bracket α β).verbalSubgroup G).inv_mem hxW
    have hai := ((OuterWord.derivedWord i).verbalSubgroup G).inv_mem ha
    simpa only [paperCommutator, commutatorElement_def, inv_inv] using
      Subgroup.commutator_mem_commutator hxi hai
  have hcomm : ∀ t ∈ P, Commute t x := by
    rcases hbranch with hα | hβ
    · exact h.outerValue_centralizes_pSubgroup hp hsolv P pCore_isPGroup
        (OuterWord.verbalSubgroup_le_of_constituent hα) hx hxp hxr
    · have hswap : ProductOrderCondition (OuterWord.bracket β α) p G := by
        simpa only [ProductOrderCondition, OuterWord.values_bracket_swap β α] using h
      have hxswap : x ∈ (OuterWord.bracket β α).values G := by
        rw [OuterWord.values_bracket_swap β α]
        exact hx
      exact hswap.outerValue_centralizes_pSubgroup hp hsolv P pCore_isPGroup
        (OuterWord.verbalSubgroup_le_of_constituent hβ) hxswap hxp hxr
  have hxcent : x ∈ Subgroup.centralizer (P : Set G) := by
    intro t ht
    exact (hcomm t ht).eq
  have hxP : x ∈ P :=
    Soluble.centralizer_pCore_le_of_pPrimeCore_eq_bot hsolv p hcore hxcent
  by_contra hnx
  have hneP : (⟨x, hxP⟩ : P) ≠ 1 := by
    intro heq
    exact hnx (congrArg Subtype.val heq)
  have hdiv := (show IsPGroup p P from pCore_isPGroup).dvd_orderOf hneP
  exact hxp (by simpa only [Subgroup.orderOf_mk] using hdiv)

/-- The full forward implication for every outer commutator word in a finite
soluble group. The product-order condition still concerns single values, and
the second value may have mixed order. -/
theorem problem2135_soluble_outerWord
    {G : Type u} [Group G] [Finite G] (hsolv : Group.IsSolvable G)
    (w : OuterWord) (p : ℕ) (hp : p.Prime) (h : ProductOrderCondition w p G) :
    HasNormalPComplement p (w.verbalSubgroup G) := by
  let T : ℕ → Prop := fun n =>
    ∀ (v : OuterWord), v.defect = n →
      ∀ (K : Type u) [Group K] [Finite K], Group.IsSolvable K →
        ∀ q : ℕ, q.Prime → ProductOrderCondition v q K →
          HasNormalPComplement q (v.verbalSubgroup K)
  have main : ∀ n, T n := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih v hv K _ _ hK q hq hcond
    by_cases hzero : v.defect = 0
    · have hderived : v = OuterWord.derivedWord v.height :=
        (OuterWord.defect_eq_zero_iff v).mp hzero
      have hdcond : ProductOrderCondition (OuterWord.derivedWord v.height) q K := by
        rw [← hderived]
        exact hcond
      have hresult := problem2135_soluble_derivedWord hK v.height q hq hdcond
      rw [← hderived] at hresult
      exact hresult
    · cases v with
      | leaf => exact (hzero (by decide)).elim
      | bracket α β =>
          let : Fact q.Prime := ⟨hq⟩
          let : Group.IsSolvable K := hK
          let N := pPrimeCore q K
          let Q := K ⧸ N
          have hN : (Nat.card N).Coprime q :=
            (pPrimeCore_coprime_card (G := K) (p := q)).symm
          have hQsolv : Group.IsSolvable Q := by infer_instance
          have hquot : ProductOrderCondition (OuterWord.bracket α β) q Q :=
            hcond.quotient N hN
          have hcore : pPrimeCore q Q = ⊥ := pPrimeCore_quotient_eq_bot q
          have hne : OuterWord.bracket α β ≠
              OuterWord.derivedWord (OuterWord.bracket α β).height := by
            intro hfull
            exact hzero ((OuterWord.defect_eq_zero_iff _).mpr hfull)
          have hproper : OuterWord.properExtensionSubgroup (OuterWord.bracket α β) Q ≤
              pCore q Q := by
            refine iSup_le fun z => iSup_le fun hz => ?_
            have hprop := (OuterWord.mem_properExtensions z (OuterWord.bracket α β)).mp hz
            have hlt : z.defect < n := by
              rw [← hv]
              exact hprop.defect_lt
            have hzcond : ProductOrderCondition z q Q := by
              intro x hx y hy hxp hyp
              exact hquot x (hprop.1.values_subset hx) y (hprop.1.values_subset hy) hxp hyp
            have hzcomp : HasNormalPComplement q (z.verbalSubgroup Q) :=
              ih z.defect hlt z rfl Q hQsolv q hq hzcond
            have hzgroup : IsPGroup q (z.verbalSubgroup Q) :=
              isPGroup_of_normal_hasNormalPComplement_of_pPrimeCore_eq_bot
                hq (z.verbalSubgroup Q) hzcomp hcore
            exact le_sSup ⟨inferInstance, hzgroup⟩
          have hgroup : IsPGroup q ((OuterWord.bracket α β).verbalSubgroup Q) := by
            apply (OuterWord.bracket α β).verbalSubgroup_isPGroup_of_primeToP_values_eq_one
              q hq hQsolv
            intro x hx hxp
            exact hquot.outerValue_eq_one_of_properExtensions_le_pCore
              hq hQsolv hcore hne hproper hx hxp
          exact verbalSubgroup_hasNormalPComplement_of_quotient_isPGroup
            (OuterWord.bracket α β) hq N hN hgroup
  exact main w.defect w rfl G hsolv p hp h

end Kourovka2135
