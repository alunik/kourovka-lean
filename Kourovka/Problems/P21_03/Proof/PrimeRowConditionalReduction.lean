import Kourovka.Problems.P21_03.Proof.PrimeOrderReduction
import Kourovka.Problems.P21_03.Proof.PrimeRowReduction
import Kourovka.Problems.P21_03.Proof.PrimeTransporterCanonical
import Kourovka.Problems.P21_03.Proof.PrimeCycleProfile

/-!
# Conditional reduction to genuine finite prime rows

This file removes the redundant rectangular `(p,r)` range from the prime-row
reduction.  The remaining finite index set consists exactly of pairs with
`p` prime, `r > 0`, and available support `p*r ≤ n`.

Every extra bad conjugator is already core-simple.  We retain that condition
while placing it into a source-outside or target-outside genuine prime row,
then sum the canonical conditional row estimates.  No portrait or analytic
majorant is used here.
-/

open Subgroup
open scoped BigOperators Pointwise

namespace Kourovka213

variable {n : ℕ}

/-! ## Genuine finite row indices -/

/-- The finite set of genuine prime-cycle rows available in degree `n`. -/
def genuinePrimeRowIndices (n : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (n + 1)).product (Finset.range (n + 1))).filter fun q ↦
    q.1.Prime ∧ 0 < q.2 ∧ q.1 * q.2 ≤ n

@[simp]
theorem mem_genuinePrimeRowIndices {n p r : ℕ} :
    (p, r) ∈ genuinePrimeRowIndices n ↔
      p.Prime ∧ 0 < r ∧ p * r ≤ n := by
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    rcases h with ⟨hp, hr, hpr⟩
    have hp_le : p ≤ n := by
      calc
        p = p * 1 := by simp
        _ ≤ p * r := Nat.mul_le_mul_left p hr
        _ ≤ n := hpr
    have hr_le : r ≤ n := by
      calc
        r = 1 * r := by simp
        _ ≤ p * r := Nat.mul_le_mul_right r hp.one_le
        _ ≤ n := hpr
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, hp, hr, hpr⟩
    · exact Finset.mem_range.mpr (by omega)
    · exact Finset.mem_range.mpr (by omega)

/-! ## Core-conditioned genuine row hits -/

/-- The concrete core-simple sample space belonging to `H` and `K`. -/
noncomputable def primeRowCoreSimpleSet
    (H K : SolubleSubgroup n) : Finset (Sym n) :=
  simplePermutations (corePartition H.carrier) (corePartition K.carrier)

/-- A source-outside prime row, restricted to the core-simple sample space. -/
noncomputable def conditionedSourcePrimeRowHit
    (H K : SolubleSubgroup n) (p r : ℕ) : Finset (Sym n) :=
  conjugationHits (outsideCorePrimeRowSlice H.carrier p r)
      (primeRowSlice K.carrier p r) ∩
    primeRowCoreSimpleSet H K

/-- A target-outside prime row, restricted to the core-simple sample space. -/
noncomputable def conditionedTargetPrimeRowHit
    (H K : SolubleSubgroup n) (p r : ℕ) : Finset (Sym n) :=
  conjugationHits (primeRowSlice H.carrier p r)
      (outsideCorePrimeRowSlice K.carrier p r) ∩
    primeRowCoreSimpleSet H K

/-- Union of all core-conditioned source-outside genuine prime rows. -/
noncomputable def conditionedSourceGenuinePrimeRowHits
    (H K : SolubleSubgroup n) : Finset (Sym n) :=
  (genuinePrimeRowIndices n).biUnion fun q ↦
    conditionedSourcePrimeRowHit H K q.1 q.2

/-- Union of all core-conditioned target-outside genuine prime rows. -/
noncomputable def conditionedTargetGenuinePrimeRowHits
    (H K : SolubleSubgroup n) : Finset (Sym n) :=
  (genuinePrimeRowIndices n).biUnion fun q ↦
    conditionedTargetPrimeRowHit H K q.1 q.2

/-- The no-double-counting row event used by a refined profile estimate. -/
noncomputable def conditionedPrimeRowHit
    (H K : SolubleSubgroup n) (p r : ℕ) : Finset (Sym n) :=
  conditionedSourcePrimeRowHit H K p r ∪
    conditionedTargetPrimeRowHit H K p r

/-- Union of the combined core-conditioned genuine prime rows. -/
noncomputable def conditionedGenuinePrimeRowHits
    (H K : SolubleSubgroup n) : Finset (Sym n) :=
  (genuinePrimeRowIndices n).biUnion fun q ↦
    conditionedPrimeRowHit H K q.1 q.2

private theorem conjugate_orderOf_eq (x g : Sym n) :
    orderOf (x * g * x⁻¹) = orderOf g := by
  apply (SemiconjBy.orderOf_eq x ?_).symm
  show x * g = (x * g * x⁻¹) * x
  group

private theorem conjugate_support_card_eq (x g : Sym n) :
    (x * g * x⁻¹).support.card = g.support.card :=
  Equiv.Perm.card_support_conj

/-- Every failure remaining after core conditioning belongs to a genuine
prime row, is outside the core on at least one side, and remains inside the
core-simple sample space. -/
theorem extraBadConjugators_subset_conditioned_genuinePrimeRowHits
    (H K : SolubleSubgroup n) :
    extraBadConjugators H K ⊆
      conditionedSourceGenuinePrimeRowHits H K ∪
        conditionedTargetGenuinePrimeRowHits H K := by
  classical
  intro x hx
  have hx' :
      Disjoint (transpositionCore H.carrier)
          (conjugate (transpositionCore K.carrier) x) ∧
        ¬ Disjoint H.carrier (conjugate K.carrier x) := by
    simpa [extraBadConjugators] using hx
  have hxSimple : x ∈ primeRowCoreSimpleSet H K := by
    have hxGood : x ∈ goodConjugators (transpositionCore H.carrier)
        (transpositionCore K.carrier) :=
      mem_goodConjugators.mpr hx'.1
    rw [goodConjugators_transpositionCore_eq_simplePermutations H K] at hxGood
    exact hxGood
  obtain ⟨p, r, hp, hr, g, hgH, hgKx, hgOrder, hcycle, hsupport⟩ :=
    exists_prime_cycle_row_mem_of_not_disjoint
      H.carrier (conjugate K.carrier x) hx'.2
  let k : Sym n := x * g * x⁻¹
  have hkK : k ∈ K.carrier :=
    (mem_conjugate_iff K.carrier x g).mp hgKx
  have hkOrder : orderOf k = p := by
    rw [conjugate_orderOf_eq x g, hgOrder]
  have hkSupport : k.support.card = p * r := by
    rw [conjugate_support_card_eq x g, hsupport]
  have hkCycle : k.cycleType = Multiset.replicate r p := by
    rw [Equiv.Perm.cycleType_conj, hcycle]
  have hpr_le : p * r ≤ n := by
    rw [← hsupport]
    simpa using g.support.card_le_univ
  have hindex : (p, r) ∈ genuinePrimeRowIndices n :=
    mem_genuinePrimeRowIndices.mpr ⟨hp, hr, hpr_le⟩
  by_cases hgCore : g ∈ transpositionCore H.carrier
  · have hkNotCore : k ∉ transpositionCore K.carrier := by
      intro hkCore
      have hgConj : g ∈ conjugate (transpositionCore K.carrier) x :=
        (mem_conjugate_iff (transpositionCore K.carrier) x g).mpr hkCore
      have hgOne := Subgroup.disjoint_def.mp hx'.1 hgCore hgConj
      exact hp.ne_one (hgOrder ▸ orderOf_eq_one_iff.mpr hgOne)
    apply Finset.mem_union_right
    rw [conditionedTargetGenuinePrimeRowHits, Finset.mem_biUnion]
    refine ⟨(p, r), hindex, ?_⟩
    rw [conditionedTargetPrimeRowHit, Finset.mem_inter]
    refine ⟨mem_conjugationHits.mpr ?_, hxSimple⟩
    exact ⟨g, mem_primeRowSlice.mpr ⟨hgH, hgOrder, hcycle, hsupport⟩,
      mem_outsideCorePrimeRowSlice.mpr
        ⟨hkK, hkOrder, hkCycle, hkSupport, hkNotCore⟩⟩
  · apply Finset.mem_union_left
    rw [conditionedSourceGenuinePrimeRowHits, Finset.mem_biUnion]
    refine ⟨(p, r), hindex, ?_⟩
    rw [conditionedSourcePrimeRowHit, Finset.mem_inter]
    refine ⟨mem_conjugationHits.mpr ?_, hxSimple⟩
    exact ⟨g, mem_outsideCorePrimeRowSlice.mpr
        ⟨hgH, hgOrder, hcycle, hsupport, hgCore⟩,
      mem_primeRowSlice.mpr ⟨hkK, hkOrder, hkCycle, hkSupport⟩⟩

/-- Combined-row version of the exhaustive cover.  Keeping the source and
target alternatives inside one union is important for refined profile bounds:
a pair outside both cores is then counted once, not once in each marginal
sum. -/
theorem extraBadConjugators_subset_conditioned_genuinePrimeRows
    (H K : SolubleSubgroup n) :
    extraBadConjugators H K ⊆ conditionedGenuinePrimeRowHits H K := by
  classical
  intro x hx
  have hx' :=
    extraBadConjugators_subset_conditioned_genuinePrimeRowHits H K hx
  rcases Finset.mem_union.mp hx' with hxSource | hxTarget
  · rw [conditionedSourceGenuinePrimeRowHits, Finset.mem_biUnion] at hxSource
    obtain ⟨q, hq, hxq⟩ := hxSource
    rw [conditionedGenuinePrimeRowHits, Finset.mem_biUnion]
    exact ⟨q, hq, Finset.mem_union_left _ hxq⟩
  · rw [conditionedTargetGenuinePrimeRowHits, Finset.mem_biUnion] at hxTarget
    obtain ⟨q, hq, hxq⟩ := hxTarget
    rw [conditionedGenuinePrimeRowHits, Finset.mem_biUnion]
    exact ⟨q, hq, Finset.mem_union_right _ hxq⟩

/-! ## Conditional finite-row sum -/

/-- The one-row source-outside density bound, specialized to a genuine row. -/
theorem conditionedSourceGenuinePrimeRowHit_density_le
    (H K : SolubleSubgroup n) (hn : 123 ≤ n)
    {p r : ℕ} (hrow : (p, r) ∈ genuinePrimeRowIndices n) :
    ((conditionedSourcePrimeRowHit H K p r).card : ℝ) /
        (primeRowCoreSimpleSet H K).card ≤
      conditionedPrimeRowMajorant n
        (outsideCorePrimeRowSlice H.carrier p r)
        (primeRowSlice K.carrier p r) p r := by
  obtain ⟨_hp, hr, hpr⟩ := mem_genuinePrimeRowIndices.mp hrow
  have h := conditioned_sourceOutsidePrimeRowHit_density_le
    (corePartition H.carrier) (corePartition K.carrier) hn
    H.carrier K.carrier p r hr hpr
  rw [avoid_coreCanonicalFamily_eq_simplePermutations] at h
  simpa [conditionedSourcePrimeRowHit, primeRowCoreSimpleSet] using h

/-- The one-row target-outside density bound, specialized to a genuine row. -/
theorem conditionedTargetGenuinePrimeRowHit_density_le
    (H K : SolubleSubgroup n) (hn : 123 ≤ n)
    {p r : ℕ} (hrow : (p, r) ∈ genuinePrimeRowIndices n) :
    ((conditionedTargetPrimeRowHit H K p r).card : ℝ) /
        (primeRowCoreSimpleSet H K).card ≤
      conditionedPrimeRowMajorant n
        (primeRowSlice H.carrier p r)
        (outsideCorePrimeRowSlice K.carrier p r) p r := by
  obtain ⟨_hp, hr, hpr⟩ := mem_genuinePrimeRowIndices.mp hrow
  have h := conditioned_targetOutsidePrimeRowHit_density_le
    (corePartition H.carrier) (corePartition K.carrier) hn
    H.carrier K.carrier p r hr hpr
  rw [avoid_coreCanonicalFamily_eq_simplePermutations] at h
  simpa [conditionedTargetPrimeRowHit, primeRowCoreSimpleSet] using h

/-- Cardinal union bound over the two core-conditioned genuine row families. -/
theorem card_extraBadConjugators_le_conditioned_genuinePrimeRowSums
    (H K : SolubleSubgroup n) :
    (extraBadConjugators H K).card ≤
      (∑ q ∈ genuinePrimeRowIndices n,
        (conditionedSourcePrimeRowHit H K q.1 q.2).card) +
      (∑ q ∈ genuinePrimeRowIndices n,
        (conditionedTargetPrimeRowHit H K q.1 q.2).card) := by
  classical
  calc
    (extraBadConjugators H K).card ≤
        (conditionedSourceGenuinePrimeRowHits H K ∪
          conditionedTargetGenuinePrimeRowHits H K).card :=
      Finset.card_le_card
        (extraBadConjugators_subset_conditioned_genuinePrimeRowHits H K)
    _ ≤ (conditionedSourceGenuinePrimeRowHits H K).card +
          (conditionedTargetGenuinePrimeRowHits H K).card :=
      Finset.card_union_le _ _
    _ ≤ _ := by
      apply Nat.add_le_add
      · exact Finset.card_biUnion_le
      · exact Finset.card_biUnion_le

/-- No-double-counting cardinal union bound.  This is the correct outer
interface for the refined core/noncore overlap calculation. -/
theorem card_extraBadConjugators_le_conditioned_genuinePrimeRows
    (H K : SolubleSubgroup n) :
    (extraBadConjugators H K).card ≤
      ∑ q ∈ genuinePrimeRowIndices n,
        (conditionedPrimeRowHit H K q.1 q.2).card := by
  classical
  calc
    (extraBadConjugators H K).card ≤
        (conditionedGenuinePrimeRowHits H K).card :=
      Finset.card_le_card
        (extraBadConjugators_subset_conditioned_genuinePrimeRows H K)
    _ ≤ _ := Finset.card_biUnion_le

/-- Abstract refined-row summation.  To connect to the degree-`400` checker,
instantiate `rowMajorant (p,r)` with its exact conditioned profile row.  The
only remaining input is then the genuinely semantic one-row inequality; all
outer union, normalization, and summation steps are discharged here. -/
theorem extraBadConjugators_relative_card_le_sum_of_conditionedPrimeRowBounds
    (H K : SolubleSubgroup n) (hn : 123 ≤ n)
    (rowMajorant : ℕ × ℕ → ℝ)
    (hrow : ∀ q ∈ genuinePrimeRowIndices n,
      ((conditionedPrimeRowHit H K q.1 q.2).card : ℝ) /
          (primeRowCoreSimpleSet H K).card ≤ rowMajorant q) :
    ((extraBadConjugators H K).card : ℝ) /
        (primeRowCoreSimpleSet H K).card ≤
      ∑ q ∈ genuinePrimeRowIndices n, rowMajorant q := by
  classical
  let C := primeRowCoreSimpleSet H K
  have hCnat : 0 < C.card := by
    simpa [C, primeRowCoreSimpleSet] using
      simplePermutations_card_pos
        (corePartition H.carrier) (corePartition K.carrier) hn
  have hC : (0 : ℝ) < C.card := by exact_mod_cast hCnat
  have hcardNat :=
    card_extraBadConjugators_le_conditioned_genuinePrimeRows H K
  have hcard :
      ((extraBadConjugators H K).card : ℝ) ≤
        ∑ q ∈ genuinePrimeRowIndices n,
          ((conditionedPrimeRowHit H K q.1 q.2).card : ℝ) := by
    exact_mod_cast hcardNat
  calc
    ((extraBadConjugators H K).card : ℝ) / C.card ≤
        (∑ q ∈ genuinePrimeRowIndices n,
          ((conditionedPrimeRowHit H K q.1 q.2).card : ℝ)) / C.card :=
      div_le_div_of_nonneg_right hcard hC.le
    _ = ∑ q ∈ genuinePrimeRowIndices n,
          ((conditionedPrimeRowHit H K q.1 q.2).card : ℝ) / C.card := by
      rw [Finset.sum_div]
    _ ≤ ∑ q ∈ genuinePrimeRowIndices n, rowMajorant q := by
      apply Finset.sum_le_sum
      intro q hq
      simpa [C] using hrow q hq

/-- Relative cardinality of the complete extra-bad set is bounded by the
finite sum of the two canonical `conditionedPrimeRowMajorant` terms over
genuine prime rows. -/
theorem extraBadConjugators_relative_card_le_genuinePrimeRowMajorants
    (H K : SolubleSubgroup n) (hn : 123 ≤ n) :
    ((extraBadConjugators H K).card : ℝ) /
        (primeRowCoreSimpleSet H K).card ≤
      ∑ q ∈ genuinePrimeRowIndices n,
        (conditionedPrimeRowMajorant n
            (outsideCorePrimeRowSlice H.carrier q.1 q.2)
            (primeRowSlice K.carrier q.1 q.2) q.1 q.2 +
          conditionedPrimeRowMajorant n
            (primeRowSlice H.carrier q.1 q.2)
            (outsideCorePrimeRowSlice K.carrier q.1 q.2) q.1 q.2) := by
  classical
  let C := primeRowCoreSimpleSet H K
  have hCnat : 0 < C.card := by
    simpa [C, primeRowCoreSimpleSet] using
      simplePermutations_card_pos
        (corePartition H.carrier) (corePartition K.carrier) hn
  have hC : (0 : ℝ) < C.card := by exact_mod_cast hCnat
  have hcardNat :=
    card_extraBadConjugators_le_conditioned_genuinePrimeRowSums H K
  have hcard :
      ((extraBadConjugators H K).card : ℝ) ≤
        (∑ q ∈ genuinePrimeRowIndices n,
          ((conditionedSourcePrimeRowHit H K q.1 q.2).card : ℝ)) +
        (∑ q ∈ genuinePrimeRowIndices n,
          ((conditionedTargetPrimeRowHit H K q.1 q.2).card : ℝ)) := by
    exact_mod_cast hcardNat
  calc
    ((extraBadConjugators H K).card : ℝ) / C.card ≤
        ((∑ q ∈ genuinePrimeRowIndices n,
            ((conditionedSourcePrimeRowHit H K q.1 q.2).card : ℝ)) +
          (∑ q ∈ genuinePrimeRowIndices n,
            ((conditionedTargetPrimeRowHit H K q.1 q.2).card : ℝ))) /
          C.card :=
      div_le_div_of_nonneg_right hcard hC.le
    _ = (∑ q ∈ genuinePrimeRowIndices n,
          ((conditionedSourcePrimeRowHit H K q.1 q.2).card : ℝ) / C.card) +
        (∑ q ∈ genuinePrimeRowIndices n,
          ((conditionedTargetPrimeRowHit H K q.1 q.2).card : ℝ) / C.card) := by
      rw [add_div]
      simp only [Finset.sum_div]
    _ ≤ (∑ q ∈ genuinePrimeRowIndices n,
          conditionedPrimeRowMajorant n
            (outsideCorePrimeRowSlice H.carrier q.1 q.2)
            (primeRowSlice K.carrier q.1 q.2) q.1 q.2) +
        (∑ q ∈ genuinePrimeRowIndices n,
          conditionedPrimeRowMajorant n
            (primeRowSlice H.carrier q.1 q.2)
            (outsideCorePrimeRowSlice K.carrier q.1 q.2) q.1 q.2) := by
      apply add_le_add
      · apply Finset.sum_le_sum
        intro q hq
        simpa [C] using
          conditionedSourceGenuinePrimeRowHit_density_le H K hn hq
      · apply Finset.sum_le_sum
        intro q hq
        simpa [C] using
          conditionedTargetGenuinePrimeRowHit_density_le H K hn hq
    _ = ∑ q ∈ genuinePrimeRowIndices n,
        (conditionedPrimeRowMajorant n
            (outsideCorePrimeRowSlice H.carrier q.1 q.2)
            (primeRowSlice K.carrier q.1 q.2) q.1 q.2 +
          conditionedPrimeRowMajorant n
            (primeRowSlice H.carrier q.1 q.2)
            (outsideCorePrimeRowSlice K.carrier q.1 q.2) q.1 q.2) := by
      rw [Finset.sum_add_distrib]

/-! ## Exact no-double-counting profile rows -/

/-- The conditioned hit from one pair `(uₐ,uᵇ)` of intrinsic noncore-cycle
profiles inside a fixed prime row. -/
noncomputable def conditionedPrimeRowProfileHit
    (H K : SolubleSubgroup n) (p r ua ub : ℕ) : Finset (Sym n) :=
  conjugationHits
      (primeCycleProfileSlice (corePartition H.carrier)
        (primeRowSlice H.carrier p r) ua)
      (primeCycleProfileSlice (corePartition K.carrier)
        (primeRowSlice K.carrier p r) ub) ∩
    primeRowCoreSimpleSet H K

/-- Exact hybrid majorant for one pair of intrinsic cycle profiles. -/
noncomputable def conditionedPrimeRowProfileMajorant
    (H K : SolubleSubgroup n) (p r ua ub : ℕ) : ℝ :=
  conditionedPrimeProfileHybridMajorant n
    (primeCycleProfileSlice (corePartition H.carrier)
      (primeRowSlice H.carrier p r) ua)
    (primeCycleProfileSlice (corePartition K.carrier)
      (primeRowSlice K.carrier p r) ub)
    p r ua ub

/-- The old source/target-outside union is contained in the full row once.
This is the point where the refined argument avoids double-counting pairs
which are outside both cores. -/
theorem conditionedPrimeRowHit_subset_fullRow
    (H K : SolubleSubgroup n) (p r : ℕ) :
    conditionedPrimeRowHit H K p r ⊆
      conjugationHits (primeRowSlice H.carrier p r)
          (primeRowSlice K.carrier p r) ∩
        primeRowCoreSimpleSet H K := by
  classical
  intro x hx
  rw [conditionedPrimeRowHit] at hx
  rcases Finset.mem_union.mp hx with hxSource | hxTarget
  · rw [conditionedSourcePrimeRowHit, Finset.mem_inter] at hxSource
    obtain ⟨hxHit, hxCore⟩ := hxSource
    obtain ⟨a, ha, hb⟩ := mem_conjugationHits.mp hxHit
    have ha' : a ∈ primeRowSlice H.carrier p r := by
      obtain ⟨haH, haOrder, haCycle, haSupport, _haOutside⟩ :=
        mem_outsideCorePrimeRowSlice.mp ha
      exact mem_primeRowSlice.mpr ⟨haH, haOrder, haCycle, haSupport⟩
    exact Finset.mem_inter.mpr
      ⟨mem_conjugationHits.mpr ⟨a, ha', hb⟩, hxCore⟩
  · rw [conditionedTargetPrimeRowHit, Finset.mem_inter] at hxTarget
    obtain ⟨hxHit, hxCore⟩ := hxTarget
    obtain ⟨a, ha, hb⟩ := mem_conjugationHits.mp hxHit
    have hb' : x * a * x⁻¹ ∈ primeRowSlice K.carrier p r := by
      obtain ⟨hbK, hbOrder, hbCycle, hbSupport, _hbOutside⟩ :=
        mem_outsideCorePrimeRowSlice.mp hb
      exact mem_primeRowSlice.mpr ⟨hbK, hbOrder, hbCycle, hbSupport⟩
    exact Finset.mem_inter.mpr
      ⟨mem_conjugationHits.mpr ⟨a, ha, hb'⟩, hxCore⟩

/-- Every combined row hit lies in one intrinsic profile pair with
`0 ≤ uₐ,uᵇ ≤ r`. -/
theorem conditionedPrimeRowHit_subset_profileUnion
    (H K : SolubleSubgroup n) (p r : ℕ) :
    conditionedPrimeRowHit H K p r ⊆
      (Finset.range (r + 1)).biUnion fun ua ↦
        (Finset.range (r + 1)).biUnion fun ub ↦
          conditionedPrimeRowProfileHit H K p r ua ub := by
  classical
  intro x hx
  have hxFull := conditionedPrimeRowHit_subset_fullRow H K p r hx
  obtain ⟨hxHit, hxCore⟩ := Finset.mem_inter.mp hxFull
  obtain ⟨a, ha, hb⟩ := mem_conjugationHits.mp hxHit
  let b : Sym n := x * a * x⁻¹
  let ua := noncoreCycleCount (corePartition H.carrier) a
  let ub := noncoreCycleCount (corePartition K.carrier) b
  have hcycleA : a.cycleType = Multiset.replicate r p :=
    (mem_primeRowSlice.mp ha).2.2.1
  have hcycleB : b.cycleType = Multiset.replicate r p :=
    (mem_primeRowSlice.mp hb).2.2.1
  have hua_le : ua ≤ r := by
    calc
      ua ≤ a.cycleType.card :=
        noncoreCycleCount_le_cycleType_card (corePartition H.carrier) a
      _ = r := by simp [hcycleA]
  have hub_le : ub ≤ r := by
    calc
      ub ≤ b.cycleType.card :=
        noncoreCycleCount_le_cycleType_card (corePartition K.carrier) b
      _ = r := by simp [hcycleB]
  rw [Finset.mem_biUnion]
  refine ⟨ua, Finset.mem_range.mpr (by omega), ?_⟩
  rw [Finset.mem_biUnion]
  refine ⟨ub, Finset.mem_range.mpr (by omega), ?_⟩
  rw [conditionedPrimeRowProfileHit, Finset.mem_inter]
  refine ⟨mem_conjugationHits.mpr ⟨a, ?_, ?_⟩, hxCore⟩
  · exact mem_primeCycleProfileSlice.mpr ⟨ha, rfl⟩
  · exact mem_primeCycleProfileSlice.mpr ⟨hb, rfl⟩

/-- Cardinal union bound over the exact profile decomposition of one row. -/
theorem card_conditionedPrimeRowHit_le_profileSum
    (H K : SolubleSubgroup n) (p r : ℕ) :
    (conditionedPrimeRowHit H K p r).card ≤
      ∑ ua ∈ Finset.range (r + 1),
        ∑ ub ∈ Finset.range (r + 1),
          (conditionedPrimeRowProfileHit H K p r ua ub).card := by
  classical
  calc
    (conditionedPrimeRowHit H K p r).card ≤
        ((Finset.range (r + 1)).biUnion fun ua ↦
          (Finset.range (r + 1)).biUnion fun ub ↦
            conditionedPrimeRowProfileHit H K p r ua ub).card :=
      Finset.card_le_card (conditionedPrimeRowHit_subset_profileUnion H K p r)
    _ ≤ ∑ ua ∈ Finset.range (r + 1),
        ((Finset.range (r + 1)).biUnion fun ub ↦
          conditionedPrimeRowProfileHit H K p r ua ub).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ ua ∈ Finset.range (r + 1),
        ∑ ub ∈ Finset.range (r + 1),
          (conditionedPrimeRowProfileHit H K p r ua ub).card := by
      exact Finset.sum_le_sum fun _ua _hua ↦ Finset.card_biUnion_le

/-- The exact one-row inequality in the shape required by
`extraBadConjugators_relative_card_le_sum_of_conditionedPrimeRowBounds`. -/
theorem conditionedPrimeRowHit_density_le_profileMajorantSum
    (H K : SolubleSubgroup n) (hn : 123 ≤ n)
    {p r : ℕ} (hrow : (p, r) ∈ genuinePrimeRowIndices n) :
    ((conditionedPrimeRowHit H K p r).card : ℝ) /
        (primeRowCoreSimpleSet H K).card ≤
      ∑ ua ∈ Finset.range (r + 1),
        ∑ ub ∈ Finset.range (r + 1),
          conditionedPrimeRowProfileMajorant H K p r ua ub := by
  classical
  obtain ⟨hp, _hr, hpr⟩ := mem_genuinePrimeRowIndices.mp hrow
  let C := primeRowCoreSimpleSet H K
  have hCnat : 0 < C.card := by
    simpa [C, primeRowCoreSimpleSet] using
      simplePermutations_card_pos
        (corePartition H.carrier) (corePartition K.carrier) hn
  have hC : (0 : ℝ) < C.card := by exact_mod_cast hCnat
  have hcardNat := card_conditionedPrimeRowHit_le_profileSum H K p r
  have hcard : ((conditionedPrimeRowHit H K p r).card : ℝ) ≤
      ∑ ua ∈ Finset.range (r + 1),
        ∑ ub ∈ Finset.range (r + 1),
          ((conditionedPrimeRowProfileHit H K p r ua ub).card : ℝ) := by
    exact_mod_cast hcardNat
  calc
    ((conditionedPrimeRowHit H K p r).card : ℝ) / C.card ≤
        (∑ ua ∈ Finset.range (r + 1),
          ∑ ub ∈ Finset.range (r + 1),
            ((conditionedPrimeRowProfileHit H K p r ua ub).card : ℝ)) /
          C.card := div_le_div_of_nonneg_right hcard hC.le
    _ = ∑ ua ∈ Finset.range (r + 1),
        ∑ ub ∈ Finset.range (r + 1),
          ((conditionedPrimeRowProfileHit H K p r ua ub).card : ℝ) /
            C.card := by
      simp_rw [Finset.sum_div]
    _ ≤ ∑ ua ∈ Finset.range (r + 1),
        ∑ ub ∈ Finset.range (r + 1),
          conditionedPrimeRowProfileMajorant H K p r ua ub := by
      apply Finset.sum_le_sum
      intro ua _hua
      apply Finset.sum_le_sum
      intro ub _hub
      have hprofile := conditioned_primeCycleProfileSlice_density_le_hybrid
        (corePartition H.carrier) (corePartition K.carrier) hn
        (primeRowSlice H.carrier p r) (primeRowSlice K.carrier p r)
        p r ua ub hp.two_le hpr
        (fun a ha ↦ (mem_primeRowSlice.mp ha).2.2.1)
        (fun b hb ↦ (mem_primeRowSlice.mp hb).2.2.1)
      rw [avoid_coreCanonicalFamily_eq_simplePermutations] at hprofile
      simpa [C, conditionedPrimeRowProfileHit,
        conditionedPrimeRowProfileMajorant, primeRowCoreSimpleSet] using hprofile

/-- Fully instantiated exact-profile outer reduction.  Its right-hand side
is the finite quantity to compare with the checked profile total. -/
theorem extraBadConjugators_relative_card_le_exactProfileMajorants
    (H K : SolubleSubgroup n) (hn : 123 ≤ n) :
    ((extraBadConjugators H K).card : ℝ) /
        (primeRowCoreSimpleSet H K).card ≤
      ∑ q ∈ genuinePrimeRowIndices n,
        ∑ ua ∈ Finset.range (q.2 + 1),
          ∑ ub ∈ Finset.range (q.2 + 1),
            conditionedPrimeRowProfileMajorant H K q.1 q.2 ua ub := by
  apply extraBadConjugators_relative_card_le_sum_of_conditionedPrimeRowBounds
    H K hn
  intro q hq
  exact conditionedPrimeRowHit_density_le_profileMajorantSum H K hn hq

end Kourovka213
