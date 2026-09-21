import Kourovka2135.PrimePowerGenerators
import Kourovka2135.PGroupGeneration
import Kourovka2135.SolubleStructure

/-!
# The soluble derived-word case when the p′-core is trivial

CGM centralization and the self-centralizing p-core kill p′-order single
values. Prime-power commutator-closed generators then make the derived
subgroup a p-group, without using a focal theorem.
-/

set_option autoImplicit false
universe u
namespace Kourovka2135
variable {G : Type u} [Group G] [Finite G]

theorem ProductOrderCondition.derivedValue_eq_one_of_coprime
    {p k : ℕ} (hp : p.Prime) (hsolv : Group.IsSolvable G)
    (h : ProductOrderCondition (OuterWord.derivedWord k) p G)
    (hcore : pPrimeCore p G = ⊥) {x : G}
    (hx : x ∈ (OuterWord.derivedWord k).values G) (hxp : ¬ p ∣ orderOf x) : x = 1 := by
  letI : Fact p.Prime := ⟨hp⟩
  let P := pCore p G
  have hcomm : ∀ g ∈ P, Commute g x :=
    h.derivedValue_centralizes_pSubgroup hp P pCore_isPGroup hx hxp
      (by rw [Subgroup.normalizer_eq_top]; trivial)
  have hxcent : x ∈ Subgroup.centralizer (P : Set G) := by
    intro g hg
    exact (hcomm g hg).eq
  have hxP : x ∈ P :=
    Soluble.centralizer_pCore_le_of_pPrimeCore_eq_bot hsolv p hcore hxcent
  by_contra hne
  have hneP : (⟨x, hxP⟩ : P) ≠ 1 := by
    intro heq
    exact hne (congrArg Subtype.val heq)
  have hdiv := (show IsPGroup p P from pCore_isPGroup).dvd_orderOf hneP
  exact hxp (by simpa only [Subgroup.orderOf_mk] using hdiv)

/-- The entire derived subgroup is a p-group when the soluble ambient group
has trivial p′-core. This uses actual single-value order hypotheses. -/
theorem ProductOrderCondition.derivedSeries_isPGroup_of_pPrimeCore_eq_bot
    {p k : ℕ} (hp : p.Prime) (hsolv : Group.IsSolvable G)
    (h : ProductOrderCondition (OuterWord.derivedWord k) p G)
    (hcore : pPrimeCore p G = ⊥) : IsPGroup p (derivedSeries G k) := by
  obtain ⟨X, hX, hgen, hprime⟩ := exists_primePower_commutatorClosed_generatingSet hsolv
  have hpow : ∀ x ∈ derivedValuesOn X k, ∃ n : ℕ, x ^ p ^ n = 1 := by
    intro x hx
    obtain ⟨q, hq, n, hn⟩ := hprime x (derivedValuesOn_subset hX k hx)
    by_cases hpq : p = q
    · subst q
      exact ⟨n, by rw [← hn]; exact pow_orderOf_eq_one x⟩
    · have hxp : ¬ p ∣ orderOf x := by
        rw [hn]
        intro hdiv
        exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow hdiv))
      have hxone := h.derivedValue_eq_one_of_coprime hp hsolv hcore
        (derivedValuesOn_subset_values X k hx) hxp
      exact ⟨0, by simp [hxone]⟩
  have hgroup := isPGroup_closure_of_soluble_commutatorClosed hsolv
    (derivedValuesOn_commutatorClosed hX k) hpow
  exact hgroup.of_equiv (MulEquiv.subgroupCongr (closure_derivedValuesOn hX hgen k))

end Kourovka2135
