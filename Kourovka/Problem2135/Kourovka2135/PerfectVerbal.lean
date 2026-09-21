import Kourovka2135.GeneratingSets
import Kourovka2135.NormalComplementCore
import Mathlib.GroupTheory.IsPerfect

/-!
# Perfect groups and outer-word subgroups

Every outer-word subgroup has soluble quotient, and equals the whole group
in a perfect group. A perfect group with a normal p-complement has order prime
to p. These facts begin the nonsoluble reduction.
-/

set_option autoImplicit false
universe u
namespace Kourovka2135
variable {G : Type u} [Group G]

theorem OuterWord.derivedSeries_height_le (w : OuterWord) :
    derivedSeries G w.height ≤ w.verbalSubgroup G := by
  rw [← OuterWord.verbalSubgroup_derivedWord]
  exact Subgroup.closure_mono (w.derivedWord_values_subset w.height le_rfl)

theorem OuterWord.quotient_verbalSubgroup_isSolvable (w : OuterWord) :
    Group.IsSolvable (G ⧸ w.verbalSubgroup G) := by
  refine ⟨w.height, ?_⟩
  rw [← map_derivedSeries_eq (QuotientGroup.mk'_surjective (w.verbalSubgroup G))]
  apply ((derivedSeries G w.height).map_eq_bot_iff).mpr
  rw [QuotientGroup.ker_mk']
  exact w.derivedSeries_height_le

theorem OuterWord.isSolvable_of_verbalSubgroup (w : OuterWord)
    (hw : Group.IsSolvable (w.verbalSubgroup G)) : Group.IsSolvable G := by
  exact (Group.isSolvable_iff_subgroup_quotient (w.verbalSubgroup G)).mpr
    ⟨hw, w.quotient_verbalSubgroup_isSolvable⟩

theorem OuterWord.verbalSubgroup_eq_top_of_isPerfect (w : OuterWord) [Group.IsPerfect G] :
    w.verbalSubgroup G = ⊤ := by
  apply top_le_iff.mp
  simpa only [Group.IsPerfect.derivedSeries_eq_top] using (w.derivedSeries_height_le (G := G))

theorem subsingleton_of_isPerfect_isSolvable
    [Group.IsPerfect G] [Group.IsSolvable G] : Subsingleton G := by
  rcases subsingleton_or_nontrivial G with h | h
  · exact h
  · let := h
    exact (Group.IsPerfect.not_isSolvable G inferInstance).elim

theorem coprime_card_of_isPerfect_hasNormalPComplement
    [Group.IsPerfect G] (p : ℕ) (hp : p.Prime) (h : HasNormalPComplement p G) :
    (Nat.card G).Coprime p := by
  obtain ⟨N, hN, hcard, n, hn⟩ := h
  let : N.Normal := hN
  let : Fact p.Prime := ⟨hp⟩
  have hQ : IsPGroup p (G ⧸ N) := IsPGroup.of_card (by
    rw [← N.index_eq_card]
    exact hn)
  let : Finite (G ⧸ N) := Nat.finite_of_card_ne_zero (by
    rw [← N.index_eq_card, hn]
    exact pow_ne_zero n hp.ne_zero)
  let : Group.IsNilpotent (G ⧸ N) := hQ.isNilpotent
  let : Subsingleton (G ⧸ N) := subsingleton_of_isPerfect_isSolvable
  have htop : N = ⊤ := by
    apply top_le_iff.mp
    intro x _
    apply (QuotientGroup.eq_one_iff x).mp
    exact Subsingleton.elim _ _
  simpa only [htop, Subgroup.card_top] using hcard

end Kourovka2135
