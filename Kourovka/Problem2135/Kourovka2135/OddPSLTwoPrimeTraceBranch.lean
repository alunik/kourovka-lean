import Kourovka2135.SLTwoTracePowerPair
import Kourovka2135.OddPSLTwoTraceFrattini
import Kourovka2135.OddGoodSetMinimalObstruction

/-! The prime-field broad-trace family, with its exact remaining concrete
generation criterion. All scalar, cohomological, central-cover and full
Frattini lifting obligations are discharged here. -/

set_option autoImplicit false
noncomputable section
namespace Kourovka2135.OddPSLTwoPrimeTraceBranch
open OddPSLTwoProjectiveChart SLTwoTraceGoodSet SLTwoTraceGoodSetProjective
open SLTwoNonscalarWordValues
variable (F : Type) [Field F] [Finite F]

theorem hasOddGeneratingGoodSetOver
    (hp : (Nat.card F).Prime) (hodd : Odd (Nat.card F)) (hsize : 17 ≤ Nat.card F)
    (s : Fˣ) (hs : (s : F) + 1 ≠ 0) (hs4 : (s : F) ^ 4 ≠ 1)
    (hns : ¬ IsSquare (s : F))
    (hgen : ∀ g : SLTwo.SL2 F, g.val 0 1 ≠ 0 → g.val 1 0 ≠ 0 →
      g.val 0 0 ≠ 0 ∨ g.val 1 1 ≠ 0 →
      Subgroup.closure ({SLTwo.tor s, g} : Set (SLTwo.SL2 F)) = ⊤)
    {G : Type} [Group G] [Finite G] [Group.IsPerfect G]
    (π : G →* Q F) (hπ : Function.Surjective π)
    (hR : IsPGroup 2 π.ker) (hRΦ : π.ker ≤ frattini G) :
    HasOddGeneratingGoodSetOver π (projectiveGoodSet (F := F)) := by
  let : Fintype F := Fintype.ofFinite F
  let : Fact (Nat.card F).Prime := ⟨hp⟩
  let : CharP F (Nat.card F) := charP_of_card_eq_prime (by simp [Nat.card_eq_fintype_card])
  have h3 : (3 : F) ≠ 0 := by
    intro he
    have hd := (CharP.cast_eq_zero_iff F (Nat.card F) 3).mp he
    exact (Nat.not_dvd_of_pos_of_lt (by decide : 0 < 3) (by omega : 3 < Nat.card F)) hd
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero (OddSLTwoCenter.ringChar_ne_two F hodd)
  have hs2 : (s : F) ^ 2 ≠ 1 := by
    intro he
    apply hs4
    calc (s : F) ^ 4 = ((s : F) ^ 2) ^ 2 := by ring
         _ = 1 := by rw [he]; simp
  have hshear : ∀ t : F, t ≠ 0 →
      Subgroup.closure ({SLTwo.tor s, shear t} : Set (SLTwo.SL2 F)) = ⊤ := by
    intro t ht
    exact hgen (shear t) ht one_ne_zero (Or.inl one_ne_zero)
  have hgood := isGeneratingGoodSet_of_shear_generation s hs2 h2 (tor_mem s hs4) hshear
  exact OddPSLTwoTraceFrattini.hasOddGeneratingGoodSetOver F hodd hsize h3 hgood
    (SLTwoTracePowerPair.exists_generating_powers hp hodd s hs hns hgen) π hπ hR hRΦ

end Kourovka2135.OddPSLTwoPrimeTraceBranch

namespace Kourovka2135
open OddPSLTwoProjectiveChart SLTwoTraceGoodSetProjective

theorem OrderMinimalException.false_of_binary_prime_pslTwo_matrix_generation
    {G : Type} [Group G] [Finite G] {w : OuterWord}
    (h : OrderMinimalException w 2 G)
    (F : Type) [Field F] [Finite F]
    (hp : (Nat.card F).Prime) (hodd : Odd (Nat.card F)) (hsize : 17 ≤ Nat.card F)
    (s : Fˣ) (hs : (s : F) + 1 ≠ 0) (hs4 : (s : F) ^ 4 ≠ 1)
    (hns : ¬ IsSquare (s : F))
    (hgen : ∀ g : SLTwo.SL2 F, g.val 0 1 ≠ 0 → g.val 1 0 ≠ 0 →
      g.val 0 0 ≠ 0 ∨ g.val 1 1 ≠ 0 →
      Subgroup.closure ({SLTwo.tor s, g} : Set (SLTwo.SL2 F)) = ⊤)
    (e : (G ⧸ solubleRadical G) ≃* Q F) : False := by
  by_cases hcentral : solubleRadical G ≤ Subgroup.center G
  · exact h.false_of_central_radical_odd_pslTwo_quotient hodd (by omega) hcentral e
  let : Group.IsPerfect G := h.isPerfect Nat.prime_two
  let π := e.toMonoidHom.comp (QuotientGroup.mk' (solubleRadical G))
  have hπ : Function.Surjective π :=
    e.surjective.comp (QuotientGroup.mk'_surjective (solubleRadical G))
  have hker : π.ker = solubleRadical G :=
    (MonoidHom.ker_mulEquiv_comp (QuotientGroup.mk' (solubleRadical G)) e).trans
      (QuotientGroup.ker_mk' (solubleRadical G))
  have hR : IsPGroup 2 π.ker := by
    rw [hker, h.radical_eq_pCore Nat.prime_two]
    exact pCore_isPGroup
  have hRΦ : π.ker ≤ frattini G := by
    rw [hker]
    exact h.radical_le_frattini Nat.prime_two
  have hgood := OddPSLTwoPrimeTraceBranch.hasOddGeneratingGoodSetOver F hp hodd hsize
    s hs hs4 hns hgen π hπ hR hRΦ
  exact h.no_odd_generating_good_set_over_nontrivial hcentral π _ one_not_mem hgood

end Kourovka2135
