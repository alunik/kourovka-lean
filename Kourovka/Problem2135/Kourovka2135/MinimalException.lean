import Kourovka2135.SolubleOuter
import Kourovka2135.PerfectVerbal
import Kourovka2135.NormalComplementOperations

/-!
# First reductions of an order-minimal counterexample

The minimality hypothesis records the full theorem for strictly smaller finite
groups. It is a local counterexample-reduction hypothesis, not an assumption on
the final target. The soluble theorem excludes soluble exceptions.
-/

set_option autoImplicit false
universe u
namespace Kourovka2135

structure OrderMinimalException (w : OuterWord) (p : ℕ) (G : Type u)
    [Group G] [Finite G] : Prop where
  condition : ProductOrderCondition w p G
  failure : ¬ HasNormalPComplement p (w.verbalSubgroup G)
  smaller : ∀ (H : Type u) [Group H] [Finite H], Nat.card H < Nat.card G →
    ProductOrderCondition w p H → HasNormalPComplement p (w.verbalSubgroup H)

variable {G : Type u} [Group G] [Finite G] {w : OuterWord} {p : ℕ}

theorem OrderMinimalException.not_isSolvable (h : OrderMinimalException w p G)
    (hp : p.Prime) : ¬ Group.IsSolvable G :=
  fun hsolv => h.failure (problem2135_soluble_outerWord hsolv w p hp h.condition)

theorem OrderMinimalException.pPrimeCore_eq_bot (h : OrderMinimalException w p G)
    (hp : p.Prime) : pPrimeCore p G = ⊥ := by
  let : Fact p.Prime := ⟨hp⟩
  let N := pPrimeCore p G
  by_contra hne
  have hcardN : 1 < Nat.card N := by
    have hpos : 0 < Nat.card N := Nat.card_pos
    have hn1 : Nat.card N ≠ 1 := fun hn => hne (Subgroup.card_eq_one.mp hn)
    omega
  have hlt : Nat.card (G ⧸ N) < Nat.card G := by
    have hpos : 0 < Nat.card (G ⧸ N) := Nat.card_pos
    have hmul := N.index_mul_card
    rw [N.index_eq_card] at hmul
    nlinarith
  have hN : (Nat.card N).Coprime p := (pPrimeCore_coprime_card (G := G) (p := p)).symm
  have hQ := h.smaller (G ⧸ N) hlt (h.condition.quotient N hN)
  exact h.failure (verbalSubgroup_hasNormalPComplement_of_quotient w hp N hN hQ)

theorem pPrimeCore_eq_bot_of_normal_subgroup
    (hp : p.Prime) (H : Subgroup G) [H.Normal] (hcore : pPrimeCore p G = ⊥) :
    pPrimeCore p H = ⊥ := by
  let : Fact p.Prime := ⟨hp⟩
  have hcard : p.Coprime (Nat.card ((pPrimeCore p H).map H.subtype)) := by
    simpa only [Subgroup.card_subtype] using (pPrimeCore_coprime_card (G := H) (p := p))
  have hmap := (pPrimeCore_eq_bot_iff.mp hcore)
    ((pPrimeCore p H).map H.subtype) inferInstance hcard
  apply Subgroup.map_injective H.subtype_injective
  simpa only [Subgroup.map_bot] using hmap

theorem OrderMinimalException.proper_normal_isSolvable
    (h : OrderMinimalException w p G) (hp : p.Prime)
    (H : Subgroup G) [H.Normal] (hne : H ≠ ⊤) : Group.IsSolvable H := by
  have hlt : Nat.card H < Nat.card G := by
    simpa only [Subgroup.card_top] using
      (Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hne))
  have hcomp := h.smaller H hlt (h.condition.subgroup H)
  have hcore : pPrimeCore p H = ⊥ :=
    pPrimeCore_eq_bot_of_normal_subgroup hp H (h.pPrimeCore_eq_bot hp)
  have hP : IsPGroup p (w.verbalSubgroup H) :=
    isPGroup_of_normal_hasNormalPComplement_of_pPrimeCore_eq_bot hp _ hcomp hcore
  let : Fact p.Prime := ⟨hp⟩
  let : Group.IsNilpotent (w.verbalSubgroup H) := hP.isNilpotent
  exact w.isSolvable_of_verbalSubgroup (by infer_instance)

theorem OrderMinimalException.isPerfect
    (h : OrderMinimalException w p G) (hp : p.Prime) : Group.IsPerfect G := by
  apply Group.isPerfect_def.mpr
  by_contra hne
  have hcomm := h.proper_normal_isSolvable hp (commutator G) hne
  have hquot : Group.IsSolvable (G ⧸ commutator G) := by
    refine ⟨1, ?_⟩
    rw [← map_derivedSeries_eq (QuotientGroup.mk'_surjective (commutator G)),
      derivedSeries_one, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  have hsolv : Group.IsSolvable G :=
    (Group.isSolvable_iff_subgroup_quotient (commutator G)).mpr ⟨hcomm, hquot⟩
  exact h.not_isSolvable hp hsolv

end Kourovka2135
