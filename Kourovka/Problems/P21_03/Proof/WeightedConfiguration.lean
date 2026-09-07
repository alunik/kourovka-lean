import Kourovka.Problems.P21_03.Proof.AtomCountArithmetic
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Fintype.Powerset

/-!
# Finite codes for weighted atom configurations

An atom portrait chooses an unordered set of locations, a positive composition
of its total support, and labels whose cardinalities multiply to one exponential
in that total support.  This file packages the generic finite arithmetic, leaving
the recursive extraction of the portrait to the forest module.
-/

open scoped BigOperators

namespace Kourovka213

universe u

/-- A convenient finite code for an unordered set of `k` sites, positive weights
summing to `s`, and an aggregate label with `D ^ s` possibilities. -/
abbrev WeightedConfigurationCode (Site : Type u) [Fintype Site]
    (D s k : ℕ) :=
  {L : Finset Site // L.card = k} ×
    {c : Composition s // c.length = k} × Fin (D ^ s)

/-- The number of weighted configuration codes has the expected binomial,
composition, and label factors. -/
theorem card_weightedConfigurationCode_le
    (Site : Type u) [Fintype Site] [DecidableEq Site] (D s k : ℕ) :
    Fintype.card (WeightedConfigurationCode Site D s k) ≤
      (Fintype.card Site).choose k * 2 ^ s * D ^ s := by
  have hcomp : Fintype.card {c : Composition s // c.length = k} ≤ 2 ^ s := by
    calc
      Fintype.card {c : Composition s // c.length = k} ≤
          Fintype.card (Composition s) :=
        Fintype.card_le_of_injective Subtype.val Subtype.val_injective
      _ = 2 ^ (s - 1) := composition_card s
      _ ≤ 2 ^ s := Nat.pow_le_pow_right (by omega) (Nat.sub_le s 1)
  simp only [Fintype.card_prod, Fintype.card_finset_len, Fintype.card_fin]
  calc
    (Fintype.card Site).choose k *
        (Fintype.card {c : Composition s // c.length = k} * D ^ s) ≤
        (Fintype.card Site).choose k * (2 ^ s * D ^ s) := by
      exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hcomp)
    _ = (Fintype.card Site).choose k * 2 ^ s * D ^ s := by ac_rfl

/-- Dependent labels with `D ^ w(i)` choices can be packed into a single
`D ^ s` label when the weights sum to `s`. -/
noncomputable def dependentFinLabelEquiv
    {ι : Type u} [Fintype ι] (D s : ℕ) (w : ι → ℕ)
    (hsum : ∑ i, w i = s) :
    (∀ i, Fin (D ^ w i)) ≃ Fin (D ^ s) := by
  classical
  apply Fintype.equivOfCardEq
  simp only [Fintype.card_pi, Fintype.card_fin]
  simp only [Finset.prod_pow_eq_pow_sum, hsum]

/-- Raw weighted data in the form naturally produced by a recursive atom portrait. -/
structure RawWeightedConfiguration (Site : Type u) [Fintype Site]
    (D s k : ℕ) where
  locations : Finset Site
  card_locations : locations.card = k
  weight : locations → ℕ
  weight_pos : ∀ x, 0 < weight x
  weight_sum : ∑ x, weight x = s
  label : ∀ x, Fin (D ^ weight x)

/-- Sort the unordered sites and read their positive weights as a composition. -/
noncomputable def RawWeightedConfiguration.weightComposition
    {Site : Type u} [Fintype Site] [LinearOrder Site]
    (c : RawWeightedConfiguration Site D s k) : Composition s where
  blocks := List.ofFn fun i : Fin k =>
    c.weight (c.locations.orderIsoOfFin c.card_locations i)
  blocks_pos := by
    simp only [List.forall_mem_ofFn_iff]
    exact fun i => c.weight_pos _
  blocks_sum := by
    rw [List.sum_ofFn]
    exact ((c.locations.orderIsoOfFin c.card_locations).toEquiv.sum_comp c.weight).trans
      c.weight_sum

@[simp]
theorem RawWeightedConfiguration.weightComposition_length
    {Site : Type u} [Fintype Site] [LinearOrder Site]
    (c : RawWeightedConfiguration Site D s k) :
    c.weightComposition.length = k := by
  change (List.ofFn fun i : Fin k =>
    c.weight (c.locations.orderIsoOfFin c.card_locations i)).length = k
  simp

/-- The canonical finite code associated to raw weighted data. -/
noncomputable def RawWeightedConfiguration.toCode
    {Site : Type u} [Fintype Site] [LinearOrder Site]
    (c : RawWeightedConfiguration Site D s k) :
    WeightedConfigurationCode Site D s k :=
  (⟨c.locations, c.card_locations⟩,
    ⟨c.weightComposition, c.weightComposition_length⟩,
    dependentFinLabelEquiv D s c.weight c.weight_sum c.label)

/-- Sorting the sites and packing all dependent labels loses no information. -/
theorem RawWeightedConfiguration.toCode_injective
    {Site : Type u} [Fintype Site] [LinearOrder Site] :
    Function.Injective
      (RawWeightedConfiguration.toCode :
        RawWeightedConfiguration Site D s k →
          WeightedConfigurationCode Site D s k) := by
  intro c d h
  have hloc : c.locations = d.locations :=
    congrArg (fun z : WeightedConfigurationCode Site D s k => z.1.1) h
  rcases c with ⟨L, hL, w, hwpos, hwsum, label⟩
  rcases d with ⟨L', hL', w', hwpos', hwsum', label'⟩
  dsimp only at hloc
  subst L'
  have hh : hL' = hL := Subsingleton.elim _ _
  cases hh
  have hblocks :
      (RawWeightedConfiguration.weightComposition
        ⟨L, hL, w, hwpos, hwsum, label⟩).blocks =
      (RawWeightedConfiguration.weightComposition
        ⟨L, hL, w', hwpos', hwsum', label'⟩).blocks :=
    congrArg
      (fun z : WeightedConfigurationCode Site D s k => z.2.1.1.blocks) h
  simp only [RawWeightedConfiguration.weightComposition] at hblocks
  have hordered :
      (fun i : Fin k => w (L.orderIsoOfFin hL i)) =
        fun i : Fin k => w' (L.orderIsoOfFin hL i) :=
    List.ofFn_injective hblocks
  have hw : w = w' := by
    funext x
    have hx := congrFun hordered ((L.orderIsoOfFin hL).symm x)
    simpa using hx
  subst w'
  have hsum : hwsum' = hwsum := Subsingleton.elim _ _
  cases hsum
  have hlabelPacked :
      dependentFinLabelEquiv D s w hwsum label =
        dependentFinLabelEquiv D s w hwsum label' :=
    congrArg (fun z : WeightedConfigurationCode Site D s k => z.2.2) h
  have hlabel : label = label' :=
    (dependentFinLabelEquiv D s w hwsum).injective hlabelPacked
  subst label'
  rfl

/-- Raw weighted configurations embed into the standard finite code. -/
noncomputable def rawWeightedConfigurationEmbedding
    (Site : Type u) [Fintype Site] [LinearOrder Site] (D s k : ℕ) :
    RawWeightedConfiguration Site D s k ↪
      WeightedConfigurationCode Site D s k where
  toFun := RawWeightedConfiguration.toCode
  inj' := RawWeightedConfiguration.toCode_injective

noncomputable instance [Fintype Site] [LinearOrder Site] :
    Fintype (RawWeightedConfiguration Site D s k) := by
  letI : Finite (RawWeightedConfiguration Site D s k) :=
    Finite.of_injective
      (rawWeightedConfigurationEmbedding Site D s k)
      (rawWeightedConfigurationEmbedding Site D s k).injective
  exact Fintype.ofFinite _

/-- Cardinal bound in the raw dependent-label representation. -/
theorem card_rawWeightedConfiguration_le
    (Site : Type u) [Fintype Site] [LinearOrder Site] (D s k : ℕ) :
    Fintype.card (RawWeightedConfiguration Site D s k) ≤
      (Fintype.card Site).choose k * 2 ^ s * D ^ s :=
  (Fintype.card_le_of_injective
    (rawWeightedConfigurationEmbedding Site D s k)
    (rawWeightedConfigurationEmbedding Site D s k).injective).trans
      (card_weightedConfigurationCode_le Site D s k)

/-- The elementary bound `s + 1 ≤ 2^s`, in the positive range. -/
theorem succ_le_two_pow_of_pos (s : ℕ) (hs : 0 < s) :
    s + 1 ≤ 2 ^ s := by
  induction s with
  | zero => omega
  | succ s ih =>
      by_cases hs0 : s = 0
      · subst s
        norm_num
      · have hspos : 0 < s := Nat.pos_of_ne_zero hs0
        calc
          s + 1 + 1 ≤ 2 * (s + 1) := by omega
          _ ≤ 2 * 2 ^ s := Nat.mul_le_mul_left 2 (ih hspos)
          _ = 2 ^ (s + 1) := by rw [pow_succ]; omega

/-- Summing over all possible atom counts still costs only a fixed exponential.
The unordered location choice supplies the factorial saving needed after the
support denominator is cleared. -/
theorem sum_choose_label_mul_support_pow_le
    (n s q D : ℕ) (hs : 1 ≤ s) (hsn : s ≤ n) (hqs : 2 * q ≤ s) :
    (∑ k ∈ Finset.range (q + 1), n.choose k * 2 ^ s * D ^ s) * s ^ q ≤
      (16 * D) ^ s * n ^ q := by
  have hqle : q ≤ s := by omega
  have hqsucc : q + 1 ≤ 2 ^ s :=
    (Nat.add_le_add_right hqle 1).trans (succ_le_two_pow_of_pos s (by omega))
  calc
    (∑ k ∈ Finset.range (q + 1), n.choose k * 2 ^ s * D ^ s) * s ^ q =
        ∑ k ∈ Finset.range (q + 1),
          (n.choose k * s ^ q) * 2 ^ s * D ^ s := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _hk
      ac_rfl
    _ ≤ ∑ _k ∈ Finset.range (q + 1),
          (4 ^ s * n ^ q) * 2 ^ s * D ^ s := by
      apply Finset.sum_le_sum
      intro k hk
      have hklt : k < q + 1 := Finset.mem_range.mp hk
      have hkq : k ≤ q := by omega
      have htwo : 2 * k ≤ s :=
        (Nat.mul_le_mul_left 2 hkq).trans hqs
      simpa [mul_assoc] using Nat.mul_le_mul_right (2 ^ s * D ^ s)
        (choose_mul_support_pow_le_four_pow_mul_degree_pow n s k q
          (hkq.trans (hqle.trans hsn)) htwo hkq hqle hsn)
    _ = (q + 1) * ((4 ^ s * n ^ q) * 2 ^ s * D ^ s) := by simp
    _ ≤ 2 ^ s * ((4 ^ s * n ^ q) * 2 ^ s * D ^ s) :=
      Nat.mul_le_mul_right _ hqsucc
    _ = (16 * D) ^ s * n ^ q := by
      rw [show 16 = 2 * 2 * 4 by norm_num]
      simp only [Nat.mul_pow]
      ac_rfl

/-- Site types of cardinality at most `n` satisfy the same summed bound. -/
theorem sum_card_weightedConfigurationCode_mul_support_pow_le
    (Site : Type u) [Fintype Site] [DecidableEq Site]
    (n s q D : ℕ) (hsite : Fintype.card Site ≤ n)
    (hs : 1 ≤ s) (hsn : s ≤ n) (hqs : 2 * q ≤ s) :
    (∑ k ∈ Finset.range (q + 1),
        Fintype.card (WeightedConfigurationCode Site D s k)) * s ^ q ≤
      (16 * D) ^ s * n ^ q := by
  apply (Nat.mul_le_mul_right (s ^ q) (Finset.sum_le_sum ?_)).trans
    (sum_choose_label_mul_support_pow_le n s q D hs hsn hqs)
  intro k _hk
  exact (card_weightedConfigurationCode_le Site D s k).trans
    (by simpa [mul_assoc] using
      Nat.mul_le_mul_right (2 ^ s * D ^ s) (Nat.choose_le_choose k hsite))

end Kourovka213
