import Kourovka2135.FrattiniDifferenceValues
import Kourovka2135.CentralPrimeActions

/-!
# Conditional centralization for an arbitrary outer word

The proof follows the leftmost branch of the word. At each bracket it constructs
single values in the conjugacy-difference set whose quotient images generate
the moving subgroup. It uses no closure-under-powers assertion for word values.
-/

set_option autoImplicit false
universe u
namespace Kourovka2135
open AbelianDifference
open scoped IsMulCommutative
variable {G : Type u} [Group G]

theorem closure_image_differenceValues_eq
    (P : Subgroup G) [P.Normal] [IsMulCommutative (FrattiniQuotient P)]
    (p : ℕ) (x : G) (s : OuterWord)
    (hactors : ∀ t, OuterWord.Constituent t s →
      frattiniConj P x ∈ Subgroup.closure (frattiniConj P '' centralPrimeValues t p x))
    (hmove : (movingSubgroup (frattiniConj P x)).map (delta (frattiniConj P x)) =
      movingSubgroup (frattiniConj P x)) :
    Subgroup.closure ((QuotientGroup.mk' (frattini P)) '' differenceValues P x s) =
      movingSubgroup (frattiniConj P x) := by
  induction s with
  | leaf =>
      rw [image_differenceValues_leaf]
      exact Subgroup.closure_eq _
  | bracket l r ihl _ =>
      let q := QuotientGroup.mk' (frattini P)
      let M := movingSubgroup (frattiniConj P x)
      let B := frattiniConj P '' centralPrimeValues r p x
      have hleft : Subgroup.closure (q '' differenceValues P x l) = M :=
        ihl (fun t ht => hactors t (.left ht))
      have hB : ∀ b ∈ B, M.map b.toMonoidHom = M := by
        rintro _ ⟨b, hb, rfl⟩
        exact map_movingSubgroup_eq_of_commute (hb.2.2.symm.map (frattiniConj P))
      have hgen : Subgroup.closure (differenceSet (q '' differenceValues P x l) B) = M :=
        closure_differenceSet_eq M (q '' differenceValues P x l) B (frattiniConj P x)
          hleft hB (hactors r (.right (.refl r))) hmove
      have hsub : differenceSet (q '' differenceValues P x l) B ⊆
          q '' differenceValues P x (OuterWord.bracket l r) := by
        rintro _ ⟨_, ⟨b, hb, rfl⟩, _, ⟨d, hd, rfl⟩, rfl⟩
        obtain ⟨c, hc, heq⟩ := exists_parent_difference_value P hd hb.1 hb.2.2
        exact ⟨c, hc, heq⟩
      apply le_antisymm
      · exact (Subgroup.closure_le _).mpr
          (image_differenceValues_subset_movingSubgroup P x (OuterWord.bracket l r))
      · change M ≤ Subgroup.closure (q '' differenceValues P x (OuterWord.bracket l r))
        rw [← hgen]
        exact Subgroup.closure_mono hsub

/-- Conditional centralization for every outer word in a finite soluble group.
The normal p-subgroup may be nonabelian, and x is an actual single word value. -/
theorem ProductOrderCondition.outerValue_centralizes_pSubgroup
    [Finite G] {p : ℕ} (hp : p.Prime) (hsolv : Group.IsSolvable G)
    {α β r : OuterWord} (h : ProductOrderCondition (OuterWord.bracket α β) p G)
    (P : Subgroup G) [P.Normal] (hP : IsPGroup p P)
    (hα : α.verbalSubgroup G ≤ r.verbalSubgroup G)
    {x : G} (hx : x ∈ (OuterWord.bracket α β).values G)
    (hxp : ¬ p ∣ orderOf x)
    (hxr : ∀ a ∈ r.verbalSubgroup G, paperCommutator x a ∈ P) :
    ∀ t ∈ P, Commute t x := by
  let : Fact p.Prime := ⟨hp⟩
  let : IsMulCommutative (FrattiniQuotient P) := frattiniQuotient_isMulCommutative p hp P hP
  let q := QuotientGroup.mk' (frattini P)
  let a := frattiniConj P x
  let M := movingSubgroup a
  have hcop : (orderOf x).Coprime (Nat.card (FrattiniQuotient P)) := by
    obtain ⟨k, hk⟩ := (frattiniQuotient_isPGroup p P hP).exists_card_eq
    rw [hk]
    exact (hp.coprime_iff_not_dvd.mpr hxp).symm.pow_right k
  have hpow : a ^ orderOf x = 1 := by
    change (frattiniConj P x) ^ orderOf x = 1
    rw [← map_pow, pow_orderOf_eq_one, map_one]
  have hmove : M.map (delta a) = M := map_delta_movingSubgroup_eq a (orderOf x) hpow hcop
  have hactors (s : OuterWord) (hs : OuterWord.Constituent s β) :
      a ∈ Subgroup.closure (frattiniConj P '' centralPrimeValues s p x) :=
    constituent_action_generated_by_centralPrimeValues p hp hsolv P hP α β r hα hx hxp hxr s hs
  have hvalues : Subgroup.closure (q '' differenceValues P x β) = M :=
    closure_image_differenceValues_eq P p x β hactors hmove
  let B := frattiniConj P '' centralPrimeValues α p x
  have haB : a ∈ Subgroup.closure B :=
    left_branch_action_generated_by_centralPrimeValues p hp hsolv P hP α β r hα hx hxp hxr
  have hfixB : ∀ b ∈ B, ∀ v ∈ M, b v = v := by
    rintro _ ⟨b, hb, rfl⟩
    rw [← hvalues]
    apply fixes_closure
    rintro _ ⟨d, hd, rfl⟩
    have hcval : paperCommutator (d : G) b ∈ (OuterWord.bracket α β).values G := by
      rw [OuterWord.values_bracket_swap]
      exact (OuterWord.mem_values_bracket β α _).mpr ⟨d, hd.2, b, hb.1, rfl⟩
    have hc := h.commutator_difference_value_eq_one hp P hP hx hxp hd.1 hb.2.2.symm hcval
    have he : d⁻¹ * MulAut.conjNormal b⁻¹ d = (1 : P) := by
      apply Subtype.ext
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv, MulAut.conjNormal_apply,
        inv_inv, Subgroup.coe_one, paperCommutator, mul_assoc] using hc
    have hdelta : delta ((frattiniConj P b)⁻¹) (q d) = 1 := by
      rw [← frattiniQuotient_paperCommutator P d b, he, map_one]
    have hfix := (delta_eq_one_iff ((frattiniConj P b)⁻¹) (q d)).mp hdelta
    have hh := congrArg (frattiniConj P b) hfix
    simpa only [MulAut.apply_inv_self] using hh.symm
  have hfix : ∀ v ∈ M, a v = v := fixes_of_mem_closure M B hfixB haB
  have hq : frattiniConj P x = 1 :=
    eq_one_of_movingSubgroup_eq_bot a (movingSubgroup_eq_bot_of_fixes a hmove hfix)
  exact centralizes_of_frattiniConj_eq_one p hp P hP hxp hq

end Kourovka2135
