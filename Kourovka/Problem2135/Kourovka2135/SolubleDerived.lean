import Kourovka2135.DerivedPGroup
import Kourovka2135.PPrimeCoreQuotient
import Kourovka2135.VerbalQuotientComplement

/-!
# Kourovka 21.35 for every derived word in a finite soluble group

This closes the derived-word soluble base case. It combines the p′-core
quotient, single-value centralization, prime-power commutator-closed generators,
and the kernel normal-complement witness. It uses no assumed focal theorem.
-/

set_option autoImplicit false
universe u
namespace Kourovka2135

/-- The full forward implication for every balanced derived word, including
δ₀, in every finite soluble group. The second value may have mixed order. -/
theorem problem2135_soluble_derivedWord
    {G : Type u} [Group G] [Finite G] (hsolv : Group.IsSolvable G)
    (k p : ℕ) (hp : p.Prime)
    (h : ProductOrderCondition (OuterWord.derivedWord k) p G) :
    HasNormalPComplement p ((OuterWord.derivedWord k).verbalSubgroup G) := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : Group.IsSolvable G := hsolv
  let N := pPrimeCore p G
  have hN : (Nat.card N).Coprime p :=
    (pPrimeCore_coprime_card (G := G) (p := p)).symm
  have hquot : ProductOrderCondition (OuterWord.derivedWord k) p (G ⧸ N) :=
    h.quotient N hN
  have hcore : pPrimeCore p (G ⧸ N) = ⊥ := pPrimeCore_quotient_eq_bot p
  have hderived : IsPGroup p (derivedSeries (G ⧸ N) k) :=
    hquot.derivedSeries_isPGroup_of_pPrimeCore_eq_bot hp (by infer_instance) hcore
  have hverbal : IsPGroup p ((OuterWord.derivedWord k).verbalSubgroup (G ⧸ N)) :=
    hderived.of_equiv (MulEquiv.subgroupCongr (OuterWord.verbalSubgroup_derivedWord k).symm)
  exact verbalSubgroup_hasNormalPComplement_of_quotient_isPGroup
    (OuterWord.derivedWord k) hp N hN hverbal

end Kourovka2135
