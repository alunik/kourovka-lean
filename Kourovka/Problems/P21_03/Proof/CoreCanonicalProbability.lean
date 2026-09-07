import Kourovka.Problems.P21_03.Proof.CoreCanonicalEvents
import Kourovka.Problems.P21_03.Proof.CorePartition

/-!
# Positive and quantitatively large core-simple sample space

The explicit local-lemma constants from `WeightedCanonicalLLL` are now
specialized to the concrete collision family.  For every `n >= 123` the
core-simple set is nonempty, and its reciprocal density is less than
`2^15`.
-/

open scoped BigOperators

namespace Kourovka213

variable {n : ℕ}

private theorem coreCanonicalWeight_eq
    (P Q : BoundedPartition n) (hn : 123 ≤ n)
    (w : CollisionWitness P Q) :
    (coreCanonicalFamily P Q w).weight (3 / 2 : Real) =
      conditionedCoreWeight n := by
  have hn2 : 2 ≤ n := by omega
  have hnR : (2 : Real) ≤ n := by exact_mod_cast hn2
  have hn0 : (n : Real) ≠ 0 := ne_of_gt (by linarith)
  have hn1 : (n : Real) - 1 ≠ 0 := ne_of_gt (by linarith)
  rw [CanonicalPartialMatching.weight, CanonicalPartialMatching.denominator,
    coreCanonicalFamily_size, Nat.cast_descFactorial_two,
    Fintype.card_fin]
  rw [conditionedCoreWeight]
  field_simp [hn0, hn1]
  <;> ring

/-- The number of concrete core events satisfies the quadratic cap used in
the inverse-density estimate. -/
theorem coreCanonicalFamily_card_le_cap (P Q : BoundedPartition n) :
    Fintype.card (CollisionWitness P Q) ≤ conditionedCoreEventCap n := by
  have hP := P.two_mul_card_pairIn_le_three_mul
  have hQ := Q.two_mul_card_pairIn_le_three_mul
  have hfour :
      4 * Fintype.card P.PairIn * Fintype.card Q.PairIn ≤ 9 * n ^ 2 := by
    calc
      4 * Fintype.card P.PairIn * Fintype.card Q.PairIn =
          (2 * Fintype.card P.PairIn) *
            (2 * Fintype.card Q.PairIn) := by ring
      _ ≤ (3 * n) * (3 * n) := Nat.mul_le_mul hP hQ
      _ = 9 * n ^ 2 := by ring
  rw [CollisionWitness.card_eq_two_mul, conditionedCoreEventCap]
  apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).mpr
  calc
    (2 * Fintype.card P.PairIn * Fintype.card Q.PairIn) * 2 =
        4 * Fintype.card P.PairIn * Fintype.card Q.PairIn := by ring
    _ ≤ 9 * n ^ 2 := hfour
    _ ≤ 9 * n ^ 2 + 1 := by omega

/-- Concrete weighted local-lemma lower bound for the core-simple set. -/
theorem coreCanonical_lll_lower
    (P Q : BoundedPartition n) (hn : 123 ≤ n) :
    (∏ w : CollisionWitness P Q,
        (1 - conditionedCoreWeight n)) *
        Fintype.card (Sym n) ≤
      ((simplePermutations P Q).card : Real) := by
  classical
  let C := coreCanonicalFamily P Q
  have hb := conditionedCoreWeight_bounds hn
  have hweight : ∀ w : CollisionWitness P Q,
      (C w).weight (3 / 2 : Real) = conditionedCoreWeight n := by
    intro w
    exact coreCanonicalWeight_eq P Q hn w
  have hpenalty : ∀ w : CollisionWitness P Q,
      1 ≤ (3 / 2 : Real) ^ (C w).size *
        ∏ v ∈ CanonicalPartialMatching.neighborhood C w,
          (1 - (C v).weight (3 / 2 : Real)) := by
    intro w
    have hprod := conditionedCoreWeight_core_product hn
      (CanonicalPartialMatching.neighborhood C w)
      (by simpa [C] using coreCanonicalFamily_neighborhood_card_le P Q w)
    calc
      (1 : Real) = (3 / 2 : Real) ^ 2 * (4 / 9 : Real) := by norm_num
      _ ≤ (3 / 2 : Real) ^ 2 *
          ∏ _v ∈ CanonicalPartialMatching.neighborhood C w,
            (1 - conditionedCoreWeight n) :=
        mul_le_mul_of_nonneg_left hprod (by positivity)
      _ = (3 / 2 : Real) ^ (C w).size *
          ∏ v ∈ CanonicalPartialMatching.neighborhood C w,
            (1 - (C v).weight (3 / 2 : Real)) := by
        simp_rw [hweight]
        rw [coreCanonicalFamily_size]
  have hlll := CanonicalPartialMatching.weighted_lll_of_penalty
    C (3 / 2 : Real) (by norm_num)
    (fun w ↦ by simpa [hweight w] using hb.2.1)
    hpenalty
  rw [avoid_coreCanonicalFamily_eq_simplePermutations] at hlll
  simpa only [hweight] using hlll

/-- Core simplicity has positive cardinality for every `n >= 123`. -/
theorem simplePermutations_card_pos
    (P Q : BoundedPartition n) (hn : 123 ≤ n) :
    0 < (simplePermutations P Q).card := by
  classical
  have hb := conditionedCoreWeight_bounds hn
  have hfactor : 0 < 1 - conditionedCoreWeight n := sub_pos.mpr hb.2.1
  have hprod : 0 <
      ∏ _w : CollisionWitness P Q, (1 - conditionedCoreWeight n) := by
    exact Finset.prod_pos fun _ _ ↦ hfactor
  have hsym : (0 : Real) < Fintype.card (Sym n) := by positivity
  have hlower := coreCanonical_lll_lower P Q hn
  have hcardR : (0 : Real) < (simplePermutations P Q).card :=
    (mul_pos hprod hsym).trans_le hlower
  exact_mod_cast hcardR

/-- The concrete inverse density of core-simple permutations is below the
fixed cap used by every conditioned row estimate. -/
theorem coreCanonical_inverse_density_lt
    (P Q : BoundedPartition n) (hn : 123 ≤ n) :
    (Fintype.card (Sym n) : Real) /
        (simplePermutations P Q).card < (2 : Real) ^ 15 := by
  classical
  let x := conditionedCoreWeight n
  let W := Fintype.card (CollisionWitness P Q)
  let coreProd : Real := (1 - x) ^ W
  have hcardPosNat := simplePermutations_card_pos P Q hn
  have hcardPos : (0 : Real) < (simplePermutations P Q).card := by
    exact_mod_cast hcardPosNat
  have hlower := coreCanonical_lll_lower P Q hn
  have hprodEq :
      (∏ _w : CollisionWitness P Q, (1 - x)) = coreProd := by
    simp [coreProd, W]
  rw [hprodEq] at hlower
  have hprodPos : 0 < coreProd := by
    have hb := conditionedCoreWeight_bounds hn
    exact pow_pos (sub_pos.mpr hb.2.1) W
  have hratio :
      (Fintype.card (Sym n) : Real) /
          (simplePermutations P Q).card ≤ coreProd⁻¹ := by
    apply (div_le_iff₀ hcardPos).mpr
    calc
      (Fintype.card (Sym n) : Real) ≤
          coreProd⁻¹ * (coreProd * Fintype.card (Sym n)) := by
        field_simp [ne_of_gt hprodPos]
        norm_num
      _ ≤ coreProd⁻¹ * (simplePermutations P Q).card :=
        mul_le_mul_of_nonneg_left hlower (le_of_lt (inv_pos.mpr hprodPos))
  have hinv : coreProd⁻¹ < (2 : Real) ^ 15 := by
    exact conditionedCoreWeight_inverse_product_lt_two_pow_fifteen hn
      (coreCanonicalFamily_card_le_cap P Q)
  exact hratio.trans_lt hinv

/-- Core-good conjugators are literally the concrete simple-permutation
finset. -/
theorem goodConjugators_transpositionCore_eq_simplePermutations
    (H K : SolubleSubgroup n) :
    goodConjugators (transpositionCore H.carrier)
        (transpositionCore K.carrier) =
      simplePermutations (corePartition H.carrier) (corePartition K.carrier) := by
  classical
  ext sigma
  rw [mem_goodConjugators]
  rw [disjoint_transpositionCore_conjugate_iff_isSimple]
  simp [simplePermutations]

/-- In particular the core-good conjugator set is nonempty. -/
theorem coreGoodConjugators_card_pos
    (H K : SolubleSubgroup n) (hn : 123 ≤ n) :
    0 < (goodConjugators (transpositionCore H.carrier)
      (transpositionCore K.carrier)).card := by
  rw [goodConjugators_transpositionCore_eq_simplePermutations]
  exact simplePermutations_card_pos _ _ hn

end Kourovka213
