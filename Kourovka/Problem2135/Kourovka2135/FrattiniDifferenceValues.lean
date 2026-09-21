import Kourovka2135.ConjugacyDifference
import Kourovka2135.FrattiniConjugation
import Kourovka2135.AbelianDifference

/-!
# Single difference values on the Frattini quotient

The quotient is assumed commutative explicitly. The normal subgroup itself
need not be commutative, finite, or a p-group. All word-value conditions refer
to single evaluations of the indicated word in the ambient group.
-/

set_option autoImplicit false
universe u
namespace Kourovka2135
variable {G : Type u} [Group G]

/-- The paper commutator `[x,t]`, retained as an element of the normal subgroup. -/
def conjugacyDifference (P : Subgroup G) [P.Normal] (x : G) (t : P) : P :=
  (MulAut.conjNormal x⁻¹ t)⁻¹ * t

@[simp]
theorem coe_conjugacyDifference (P : Subgroup G) [P.Normal] (x : G) (t : P) :
    (conjugacyDifference P x t : G) = paperCommutator x (t : G) := by
  simp only [conjugacyDifference, Subgroup.coe_mul, Subgroup.coe_inv,
    MulAut.conjNormal_apply, mul_inv_rev, inv_inv, paperCommutator, mul_assoc]

theorem mem_range_conjugacyDifference_iff (P : Subgroup G) [P.Normal]
    (x : G) (d : P) :
    d ∈ Set.range (conjugacyDifference P x) ↔
      (d : G) ∈ conjugacyDifferences P x := by
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨t, t.property, coe_conjugacyDifference P x t⟩
  · rintro ⟨t, ht, heq⟩
    refine ⟨⟨t, ht⟩, ?_⟩
    apply Subtype.ext
    simpa only [coe_conjugacyDifference] using heq.symm

/-- Conjugacy differences which are single values of `s` in `G`. -/
def differenceValues (P : Subgroup G) [P.Normal] (x : G)
    (s : OuterWord) : Set P :=
  {d | (d : G) ∈ conjugacyDifferences P x ∧ (d : G) ∈ s.values G}

open scoped IsMulCommutative
open AbelianDifference

section AbelianQuotient
variable (P : Subgroup G) [P.Normal]
variable [IsMulCommutative (FrattiniQuotient P)]

theorem frattiniQuotient_conjugacyDifference (x : G) (t : P) :
    (QuotientGroup.mk' (frattini P)) (conjugacyDifference P x t) =
      delta (frattiniConj P x)
        ((frattiniConj P x)⁻¹ ((QuotientGroup.mk' (frattini P)) t)) := by
  rw [conjugacyDifference, map_mul, map_inv, ← frattiniConj_apply_mk, map_inv]
  change _ = _⁻¹ * (frattiniConj P x) ((frattiniConj P x)⁻¹ _)
  rw [MulAut.apply_inv_self]

/-- The image of the entire difference set is the entire moving subgroup. -/
theorem image_conjugacyDifference (x : G) :
    (QuotientGroup.mk' (frattini P)) '' Set.range (conjugacyDifference P x) =
      (movingSubgroup (frattiniConj P x) : Set (FrattiniQuotient P)) := by
  ext v
  constructor
  · rintro ⟨d, ⟨t, rfl⟩, rfl⟩
    exact ⟨(frattiniConj P x)⁻¹ ((QuotientGroup.mk' (frattini P)) t),
      (frattiniQuotient_conjugacyDifference P x t).symm⟩
  · rintro ⟨v, rfl⟩
    obtain ⟨t, ht⟩ := QuotientGroup.mk'_surjective (frattini P) ((frattiniConj P x) v)
    refine ⟨conjugacyDifference P x t, ⟨t, rfl⟩, ?_⟩
    rw [frattiniQuotient_conjugacyDifference, ht, MulAut.inv_apply_self]

theorem image_differenceValues_subset_movingSubgroup (x : G) (s : OuterWord) :
    (QuotientGroup.mk' (frattini P)) '' differenceValues P x s ⊆
      (movingSubgroup (frattiniConj P x) : Set (FrattiniQuotient P)) := by
  rw [← image_conjugacyDifference]
  exact Set.image_mono fun d hd => (mem_range_conjugacyDifference_iff P x d).mpr hd.1

theorem image_differenceValues_leaf (x : G) :
    (QuotientGroup.mk' (frattini P)) '' differenceValues P x OuterWord.leaf =
      (movingSubgroup (frattiniConj P x) : Set (FrattiniQuotient P)) := by
  have hleaf : differenceValues P x OuterWord.leaf =
      Set.range (conjugacyDifference P x) := by
    ext d
    simp only [differenceValues, Set.mem_ofPred_eq, OuterWord.values_leaf,
      Set.mem_univ, and_true, mem_range_conjugacyDifference_iff]
  rw [hleaf, image_conjugacyDifference]

/-- The inverse automorphism is dictated by the paper's commutator convention. -/
theorem frattiniQuotient_paperCommutator (d : P) (b : G) :
    (QuotientGroup.mk' (frattini P)) (d⁻¹ * MulAut.conjNormal b⁻¹ d) =
      delta ((frattiniConj P b)⁻¹) ((QuotientGroup.mk' (frattini P)) d) := by
  rw [map_mul, map_inv, ← frattiniConj_apply_mk, map_inv]
  rfl

omit [P.Normal] in
theorem frattiniQuotient_subgroup_conjugate (u d : P) :
    (QuotientGroup.mk' (frattini P)) (u * d * u⁻¹) =
      (QuotientGroup.mk' (frattini P)) d := by
  rw [map_mul, map_mul, map_inv]
  simp [mul_comm]

/-- Passing up one word bracket preserves both the single-value condition and
the required quotient image, after conjugating inside the normal subgroup. -/
theorem exists_parent_difference_value {x : G} {s t : OuterWord} {d : P}
    (hd : d ∈ differenceValues P x s) {b : G} (hb : b ∈ t.values G)
    (hbx : Commute b x) :
    ∃ c : P, c ∈ differenceValues P x (OuterWord.bracket s t) ∧
      (QuotientGroup.mk' (frattini P)) c =
        delta ((frattiniConj P b)⁻¹) ((QuotientGroup.mk' (frattini P)) d) := by
  let e : P := d⁻¹ * MulAut.conjNormal b⁻¹ d
  have he : (e : G) = paperCommutator (d : G) b := by
    simp only [e, Subgroup.coe_mul, Subgroup.coe_inv, MulAut.conjNormal_apply,
      inv_inv, paperCommutator, mul_assoc]
  obtain ⟨u, hu, hdiff⟩ := exists_conjugate_commutator_mem_differences P hd.1 hbx.symm
  let uP : P := ⟨u, hu⟩
  let c : P := uP * e * uP⁻¹
  have hc : (c : G) = u * paperCommutator (d : G) b * u⁻¹ := by
    simp only [c, Subgroup.coe_mul, Subgroup.coe_inv, uP, he]
  have heval : paperCommutator (d : G) b ∈ (OuterWord.bracket s t).values G :=
    (OuterWord.mem_values_bracket s t _).mpr ⟨d, hd.2, b, hb, rfl⟩
  refine ⟨c, ⟨?_, ?_⟩, ?_⟩
  · simpa only [hc] using hdiff
  · rw [hc]
    simpa only [inv_inv] using (OuterWord.bracket s t).conj_mem_values heval u⁻¹
  · change (QuotientGroup.mk' (frattini P)) (uP * e * uP⁻¹) = _
    rw [frattiniQuotient_subgroup_conjugate]
    exact frattiniQuotient_paperCommutator P d b

end AbelianQuotient
end Kourovka2135
