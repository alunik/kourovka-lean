import Kourovka2135.OddOrderFromClassification
import Kourovka2135.MinimalSimpleReduction

/-! The minimal-simple quotient reduction at the prime two, without a
noncentral-radical hypothesis. Thompson's classification is explicit. This
does not exclude the remaining perfect central extensions of those models. -/

set_option autoImplicit false
universe u
namespace Kourovka2135
variable {G : Type u} [Group G] [Finite G] {w : OuterWord}

theorem OrderMinimalException.proper_perfect_eq_bot_two
    (classification : MinimalSimpleClassification.{u})
    (h : OrderMinimalException w 2 G)
    (H : Subgroup G) (hne : H ≠ ⊤) [Group.IsPerfect H] : H = ⊥ := by
  have hodd : Odd (Nat.card H) := Nat.coprime_two_right.mp
    (h.proper_perfect_coprime_card Nat.prime_two H hne)
  let : Group.IsSolvable H :=
    isSolvable_of_odd_card_of_minimalSimpleClassification classification H hodd
  let : Subsingleton H := subsingleton_of_isPerfect_isSolvable
  exact Subgroup.eq_bot_of_subsingleton H

theorem OrderMinimalException.proper_subgroup_isSolvable_two
    (classification : MinimalSimpleClassification.{u})
    (h : OrderMinimalException w 2 G)
    (H : Subgroup G) (hne : H ≠ ⊤) : Group.IsSolvable H := by
  apply isSolvable_of_perfect_subgroups_trivial
  intro K hK
  let : Group.IsPerfect K := hK
  let : Group.IsPerfect (K.map H.subtype) := Group.IsPerfect.map H.subtype
  have hmapne : K.map H.subtype ≠ ⊤ := fun heq => hne (top_le_iff.mp
    (heq ▸ Subgroup.map_subtype_le K))
  have hbot := h.proper_perfect_eq_bot_two classification (K.map H.subtype) hmapne
  apply Subgroup.map_injective H.subtype_injective
  simpa only [Subgroup.map_bot] using hbot

theorem OrderMinimalException.quotient_radical_proper_subgroup_isSolvable_two
    (classification : MinimalSimpleClassification.{u})
    (h : OrderMinimalException w 2 G)
    (H : Subgroup (G ⧸ solubleRadical G)) (hne : H ≠ ⊤) : Group.IsSolvable H := by
  let q := QuotientGroup.mk' (solubleRadical G)
  let K := H.comap q
  have hKne : K ≠ ⊤ := by
    intro heq
    apply hne
    apply Subgroup.comap_injective (QuotientGroup.mk'_surjective _)
    simpa only [Subgroup.comap_top] using heq
  let : Group.IsSolvable K := h.proper_subgroup_isSolvable_two classification K hKne
  let f : K →* H := {
    toFun := fun x => ⟨q (x : G), x.property⟩
    map_one' := Subtype.ext (map_one q)
    map_mul' := fun _ _ => Subtype.ext (map_mul q _ _) }
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (solubleRadical G) (y : G ⧸ _)
    refine ⟨⟨x, ?_⟩, Subtype.ext hx⟩
    change q x ∈ H
    rw [hx]
    exact y.property
  exact Group.isSolvable_of_surjective hf

theorem OrderMinimalException.radical_quotient_has_classified_model_two
    (classification : MinimalSimpleClassification.{u})
    (h : OrderMinimalException w 2 G) :
    IsMinimalSimpleModel (G ⧸ solubleRadical G) := by
  let : IsSimpleGroup (G ⧸ solubleRadical G) := h.quotient_radical_isSimple Nat.prime_two
  exact classification (G ⧸ solubleRadical G)
    (h.quotient_radical_not_isMulCommutative Nat.prime_two)
    (h.quotient_radical_proper_subgroup_isSolvable_two classification)

end Kourovka2135
