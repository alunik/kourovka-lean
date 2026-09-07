import Kourovka.Problems.P21_03.Proof.FourBlockWitness
import Kourovka.Problems.P21_03.Proof.ConfigurationPoisson.ConfigurationLimit
import Kourovka.Problems.P21_03.Proof.FactorialRatioBound
import Kourovka.Problems.P21_03.Proof.ConfigurationPoisson.WitnessOverlapBound
import Kourovka.Problems.P21_03.Proof.ConfigurationPoisson.CompatibleStratumBound
import Kourovka.Problems.P21_03.Proof.ConfigurationPoisson.UniformTopApproximation
import Kourovka.Problems.P21_03.Proof.UniformBrunLower
import Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib.Topology.Order.LiminfLimsup

/-!
# The explicit upper-bound witness

This file identifies the group-theoretic success probability for bounded Young subgroups
with the zero-collision probability in the configuration model.  It then records the
parameter limits for the consecutive four-block family.
-/

open Filter Asymptotics
open scoped Topology

namespace Kourovka213

/-- A count smaller by one power than its support has vanishing normalized
factorial contribution. -/
private theorem tendsto_sparse_factorial_term_zero
    (A : ℕ → ℕ) (C d : ℕ) (hd : 0 < d)
    (hA : ∀ᶠ n in atTop, A n ≤ C * n ^ (d - 1)) :
    Tendsto
      (fun n => ((A n * (n - d).factorial : ℕ) : ℝ) / n.factorial)
      atTop (nhds 0) := by
  have hnonneg : ∀ᶠ n : ℕ in atTop,
      0 ≤ ((A n * (n - d).factorial : ℕ) : ℝ) / n.factorial :=
    Eventually.of_forall fun _ => div_nonneg (by positivity) (by positivity)
  have hupper : ∀ᶠ n : ℕ in atTop,
      ((A n * (n - d).factorial : ℕ) : ℝ) / n.factorial ≤
        (C * 3 ^ d : ℕ) / (n : ℝ) := by
    filter_upwards [hA, eventually_ge_atTop d, eventually_ge_atTop 1]
      with n hAn hdn hn
    have hnSucc : n * n ^ (d - 1) = n ^ d := by
      calc
        n * n ^ (d - 1) = n ^ (d - 1) * n := Nat.mul_comm _ _
        _ = n ^ ((d - 1) + 1) := (pow_succ n (d - 1)).symm
        _ = n ^ d := by congr 1 <;> omega
    have hnat :
        n * (A n * (n - d).factorial) ≤
          (C * 3 ^ d) * n.factorial := by
      calc
        n * (A n * (n - d).factorial) ≤
            n * ((C * n ^ (d - 1)) * (n - d).factorial) :=
          Nat.mul_le_mul_left n (Nat.mul_le_mul_right _ hAn)
        _ = C * (n ^ d * (n - d).factorial) := by rw [← hnSucc]; ring
        _ ≤ C * (3 ^ d * n.factorial) :=
          Nat.mul_le_mul_left C
            (pow_mul_factorial_sub_le_three_pow_mul_factorial n d hdn)
        _ = (C * 3 ^ d) * n.factorial := by ring
    have hreal :
        (((A n * (n - d).factorial : ℕ) : ℝ) * (n : ℝ)) ≤
          ((C * 3 ^ d : ℕ) : ℝ) * (n.factorial : ℝ) := by
      exact_mod_cast (by simpa [mul_comm] using hnat)
    exact (div_le_div_iff₀ (by positivity : (0 : ℝ) < n.factorial)
      (by exact_mod_cast hn : (0 : ℝ) < n)).2 hreal
  exact squeeze_zero' hnonneg hupper
    (tendsto_const_div_atTop_nhds_zero_nat ((C * 3 ^ d : ℕ) : ℝ))

private theorem tendsto_choose_factorial_main
    (W : ℕ → ℕ) (lambda : ℝ) (hlambda : 0 < lambda)
    (hW : Tendsto (fun n => (W n : ℝ) / (n : ℝ) ^ 2) atTop (nhds lambda))
    (k : ℕ) :
    Tendsto
      (fun n => (W n).choose k * (n - 2 * k).factorial / n.factorial : ℕ → ℝ)
      atTop (nhds (lambda ^ k / (k.factorial : ℝ))) := by
  have hn2 : Tendsto (fun n : ℕ => (n : ℝ) ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp
      tendsto_natCast_atTop_atTop
  have hWreal : Tendsto (fun n => (W n : ℝ)) atTop atTop :=
    hn2.num hlambda hW
  have hWnat : Tendsto W atTop atTop := tendsto_natCast_atTop_iff.mp hWreal
  have hchooseEquiv :
      (fun n => ((W n).choose k : ℝ)) ~[atTop]
        (fun n => (W n : ℝ) ^ k / (k.factorial : ℝ)) := by
    change ((fun m : ℕ => (m.choose k : ℝ)) ∘ W) ~[atTop]
      ((fun m : ℕ => (m : ℝ) ^ k / (k.factorial : ℝ)) ∘ W)
    exact (isEquivalent_choose k).comp_tendsto hWnat
  have hdenomNonzero : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (2 * k) ≠ 0 := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    positivity
  have hchooseDensity :
      Tendsto (fun n => ((W n).choose k : ℝ) / (n : ℝ) ^ (2 * k)) atTop
        (nhds (lambda ^ k / (k.factorial : ℝ))) := by
    apply ((hchooseEquiv.div (IsEquivalent.refl :
      (fun n : ℕ => (n : ℝ) ^ (2 * k)) ~[atTop]
        (fun n : ℕ => (n : ℝ) ^ (2 * k)))).tendsto_nhds_iff).2
    convert (hW.pow k).div_const (k.factorial : ℝ) using 1
    · funext n
      simp only [Pi.div_apply]
      rw [div_pow, ← pow_mul]
      ring
  have hdescNonzero :
      ∀ᶠ n : ℕ in atTop, (n.descFactorial (2 * k) : ℝ) ≠ 0 := by
    filter_upwards [eventually_ge_atTop (2 * k)] with n hn
    exact_mod_cast (Nat.ne_of_gt (Nat.descFactorial_pos.mpr hn))
  have hfactorialCorrection' :
      Tendsto (fun n : ℕ => (n : ℝ) ^ (2 * k) /
        (n.descFactorial (2 * k) : ℝ)) atTop (nhds 1) :=
    (isEquivalent_iff_tendsto_one hdescNonzero).1
      (isEquivalent_descFactorial (2 * k)).symm
  have hfactorialCorrection :
      Tendsto (fun n : ℕ => (n : ℝ) ^ (2 * k) *
        ((n - 2 * k).factorial : ℝ) / (n.factorial : ℝ)) atTop (nhds 1) := by
    apply hfactorialCorrection'.congr'
    filter_upwards [eventually_ge_atTop (2 * k)] with n hn
    have hfac := Nat.factorial_mul_descFactorial hn
    rw [← hfac]
    have hsubne : ((n - 2 * k).factorial : ℝ) ≠ 0 := by positivity
    simpa [mul_comm] using
      (mul_div_mul_right ((n : ℝ) ^ (2 * k))
        (n.descFactorial (2 * k) : ℝ) hsubne).symm
  have hproduct := hchooseDensity.mul hfactorialCorrection
  have heq :
      (fun n => ((W n).choose k * (n - 2 * k).factorial / n.factorial : ℝ)) =ᶠ[atTop]
        (fun n => (((W n).choose k : ℝ) / (n : ℝ) ^ (2 * k)) *
          ((n : ℝ) ^ (2 * k) * ((n - 2 * k).factorial : ℝ) /
            (n.factorial : ℝ))) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnr : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    field_simp
  simpa using hproduct.congr' heq.symm

private theorem card_disjoint_add_card_overlapping_eq_choose
    (P Q : BoundedPartition n) (k : ℕ) :
    (disjointWitnessFamilies P Q k).card +
        (overlappingWitnessFamilies P Q k).card =
      (Fintype.card (CollisionWitness P Q)).choose k := by
  classical
  unfold disjointWitnessFamilies overlappingWitnessFamilies
  rw [Finset.card_filter_add_card_filter_not]
  simp [witnessFamilies]

private theorem tendsto_disjoint_factorial_main
    (P Q : ∀ n, BoundedPartition n) (lambda : ℝ) (hlambda : 0 < lambda)
    (hW : Tendsto
      (fun n => Fintype.card (CollisionWitness (P n) (Q n)) / (n : ℝ) ^ 2)
      atTop (nhds lambda)) (k : ℕ) :
    Tendsto
      (fun n => (((disjointWitnessFamilies (P n) (Q n) k).card *
        (n - 2 * k).factorial : ℕ) : ℝ) / n.factorial)
      atTop (nhds (lambda ^ k / (k.factorial : ℝ))) := by
  classical
  let W : ℕ → ℕ := fun n => Fintype.card (CollisionWitness (P n) (Q n))
  have hchoose := tendsto_choose_factorial_main W lambda hlambda
    (by simpa [W] using hW) k
  obtain rfl | k := k
  · have hcard0 (n : ℕ) :
        (disjointWitnessFamilies (P n) (Q n) 0).card = 1 := by
      have hempty : WitnessFamilyVertexDisjoint
          (∅ : Finset (CollisionWitness (P n) (Q n))) := by
        constructor <;> intro x y _ <;>
          exact (Finset.notMem_empty x.1.1 x.1.2).elim
      unfold disjointWitnessFamilies
      rw [show witnessFamilies (P n) (Q n) 0 = {∅} by
        ext S
        simp [witnessFamilies]]
      rw [Finset.filter_eq_self.2]
      · simp
      · intro S hS
        have hSeq : S = ∅ := by simpa using hS
        simpa [hSeq] using hempty
    simpa [hcard0] using hchoose
  let C : ℕ := 36 * (2 * (k + 1)) ^ 2 * 9 ^ k
  have hcardOverlap : ∀ n,
      (overlappingWitnessFamilies (P n) (Q n) (k + 1)).card ≤
        C * n ^ (2 * (k + 1) - 1) := by
    intro n
    calc
      (overlappingWitnessFamilies (P n) (Q n) (k + 1)).card ≤
          2 * (2 * (k + 1)) ^ 2 *
            ((9 * n ^ 2) ^ ((k + 1) - 1) * (18 * n)) :=
        card_overlappingWitnessFamilies_le_polynomial _ _ _
      _ = 36 * (2 * (k + 1)) ^ 2 * 9 ^ k *
          (n ^ (2 * k) * n) := by
        simp only [Nat.add_sub_cancel, mul_pow]
        rw [← pow_mul n 2 k]
        ring
      _ = C * n ^ (2 * (k + 1) - 1) := by
        dsimp [C]
        rw [← pow_succ]
        congr 2 <;> omega
  have hoverlap :
      Tendsto
        (fun n => (((overlappingWitnessFamilies (P n) (Q n) (k + 1)).card *
          (n - 2 * (k + 1)).factorial : ℕ) : ℝ) / n.factorial)
        atTop (nhds 0) :=
    tendsto_sparse_factorial_term_zero
      (fun n => (overlappingWitnessFamilies (P n) (Q n) (k + 1)).card)
      C (2 * (k + 1)) (by omega) (Eventually.of_forall hcardOverlap)
  have hoverlap' :
      Tendsto
        (fun n => ((overlappingWitnessFamilies (P n) (Q n) (k + 1)).card : ℝ) *
          ((n - 2 * (k + 1)).factorial : ℝ) / n.factorial)
        atTop (nhds 0) := by
    simpa only [Nat.cast_mul] using hoverlap
  have heq :
      (fun n => ((disjointWitnessFamilies (P n) (Q n) (k + 1)).card : ℝ) *
        ((n - 2 * (k + 1)).factorial : ℝ) / n.factorial) =
      (fun n => ((W n).choose (k + 1) : ℝ) *
          ((n - 2 * (k + 1)).factorial : ℝ) / n.factorial -
        ((overlappingWitnessFamilies (P n) (Q n) (k + 1)).card : ℝ) *
          ((n - 2 * (k + 1)).factorial : ℝ) / n.factorial) := by
    funext n
    have hc := card_disjoint_add_card_overlapping_eq_choose
      (P n) (Q n) (k + 1)
    have hcR :
        ((disjointWitnessFamilies (P n) (Q n) (k + 1)).card : ℝ) +
            (overlappingWitnessFamilies (P n) (Q n) (k + 1)).card =
          (W n).choose (k + 1) := by
      exact_mod_cast hc
    rw [← hcR]
    ring
  simpa only [Nat.cast_mul, sub_zero, W] using
    (hchoose.sub hoverlap').congr' (Eventually.of_forall fun n =>
      congrFun heq n |>.symm)

private theorem tendsto_lowerSupportContribution_zero
    (P Q : ∀ n, BoundedPartition n) (k : ℕ) (C : ℕ → ℕ)
    (hcount : ∀ r, r < 2 * k →
      ∀ᶠ n : ℕ in atTop,
        (compatibleWitnessFamiliesBySupport (P n) (Q n) k r).card ≤
          C r * n ^ (r - 1)) :
    Tendsto
      (fun n => ∑ r ∈ Finset.range (2 * k),
        (((compatibleWitnessFamiliesBySupport (P n) (Q n) k r).card *
          (n - r).factorial : ℕ) : ℝ) / n.factorial)
      atTop (nhds 0) := by
  obtain rfl | k := k
  · simpa using (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
  have hterm : ∀ r ∈ Finset.range (2 * (k + 1)),
      Tendsto
        (fun n => (((compatibleWitnessFamiliesBySupport (P n) (Q n)
          (k + 1) r).card * (n - r).factorial : ℕ) : ℝ) / n.factorial)
        atTop (nhds 0) := by
    intro r hr
    have hrlt : r < 2 * (k + 1) := Finset.mem_range.mp hr
    by_cases hrzero : r = 0
    · subst r
      have heq :
          (fun n => (((compatibleWitnessFamiliesBySupport (P n) (Q n)
            (k + 1) 0).card * n.factorial : ℕ) : ℝ) / n.factorial) =
            fun _ : ℕ => (0 : ℝ) := by
        funext n
        rw [compatibleWitnessFamiliesBySupport_zero_eq_empty _ _ (k + 1) (by omega)]
        simp
      exact (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0)).congr' (by
          exact Eventually.of_forall fun n => (congrFun heq n).symm)
    · exact tendsto_sparse_factorial_term_zero
        (fun n => (compatibleWitnessFamiliesBySupport (P n) (Q n)
          (k + 1) r).card)
        (C r) r (Nat.pos_of_ne_zero hrzero) (hcount r hrlt)
  simpa using tendsto_finsetSum (Finset.range (2 * (k + 1))) hterm

private theorem tendsto_normalizedBinomialMoment_of_support_bound
    (P Q : ∀ n, BoundedPartition n) (lambda : ℝ) (hlambda : 0 < lambda)
    (hW : Tendsto
      (fun n => Fintype.card (CollisionWitness (P n) (Q n)) / (n : ℝ) ^ 2)
      atTop (nhds lambda)) (k : ℕ) (C : ℕ → ℕ)
    (hcount : ∀ r, r < 2 * k →
      ∀ᶠ n : ℕ in atTop,
        (compatibleWitnessFamiliesBySupport (P n) (Q n) k r).card ≤
          C r * n ^ (r - 1)) :
    Tendsto
      (fun n => normalizedBinomialMoment (collisionCount (P n) (Q n)) k)
      atTop (nhds (lambda ^ k / (k.factorial : ℝ))) := by
  have hmain := tendsto_disjoint_factorial_main P Q lambda hlambda hW k
  have herror := tendsto_lowerSupportContribution_zero P Q k C hcount
  have hsum := hmain.add herror
  have hsum' :
      Tendsto
        (fun n =>
          ((disjointWitnessFamilies (P n) (Q n) k).card : ℝ) *
              ((n - 2 * k).factorial : ℝ) / n.factorial +
            ∑ r ∈ Finset.range (2 * k),
              (((compatibleWitnessFamiliesBySupport (P n) (Q n) k r).card *
                (n - r).factorial : ℕ) : ℝ) / n.factorial)
        atTop (nhds (lambda ^ k / (k.factorial : ℝ))) := by
    simpa only [Nat.cast_mul, add_zero] using hsum
  apply hsum'.congr'
  filter_upwards with n
  rw [normalizedBinomialMoment, binomialMoment_collisionCount_eq_natCast,
    card_sym, collisionBinomialMomentNat_eq_sum_support_strata,
    Finset.sum_range_succ,
    compatibleWitnessFamiliesBySupport_two_mul_eq_disjoint]
  push_cast
  rw [add_div, Finset.sum_div]
  ring

private theorem sparse_factorial_term_le_const_div
    (A C d n : ℕ) (hd : 0 < d) (hdn : d ≤ n) (hn : 1 ≤ n)
    (hA : A ≤ C * n ^ (d - 1)) :
    ((A * (n - d).factorial : ℕ) : ℝ) / n.factorial ≤
      (C * 3 ^ d : ℕ) / (n : ℝ) := by
  have hnSucc : n * n ^ (d - 1) = n ^ d := by
    calc
      n * n ^ (d - 1) = n ^ (d - 1) * n := Nat.mul_comm _ _
      _ = n ^ ((d - 1) + 1) := (pow_succ n (d - 1)).symm
      _ = n ^ d := by congr 1 <;> omega
  have hnat :
      n * (A * (n - d).factorial) ≤ (C * 3 ^ d) * n.factorial := by
    calc
      n * (A * (n - d).factorial) ≤
          n * ((C * n ^ (d - 1)) * (n - d).factorial) :=
        Nat.mul_le_mul_left n (Nat.mul_le_mul_right _ hA)
      _ = C * (n ^ d * (n - d).factorial) := by rw [← hnSucc]; ring
      _ ≤ C * (3 ^ d * n.factorial) :=
        Nat.mul_le_mul_left C
          (pow_mul_factorial_sub_le_three_pow_mul_factorial n d hdn)
      _ = (C * 3 ^ d) * n.factorial := by ring
  have hreal :
      (((A * (n - d).factorial : ℕ) : ℝ) * (n : ℝ)) ≤
        ((C * 3 ^ d : ℕ) : ℝ) * (n.factorial : ℝ) := by
    exact_mod_cast (by simpa [mul_comm] using hnat)
  exact (div_le_div_iff₀ (by positivity : (0 : ℝ) < n.factorial)
    (by exact_mod_cast hn : (0 : ℝ) < n)).2 hreal

private theorem eventually_uniform_lowerSupportContribution_lt
    (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ P Q : BoundedPartition n,
      ∑ r ∈ Finset.range (2 * k),
        (((compatibleWitnessFamiliesBySupport P Q k r).card *
          (n - r).factorial : ℕ) : ℝ) / n.factorial < ε := by
  obtain rfl | k := k
  · filter_upwards with n
    intro P Q
    simpa using hε
  let C : ℕ → ℕ := fun r =>
    (r + 1) ^ 2 * (((r * 4) ^ (2 * (k + 1))) ^ 2)
  let D : ℕ := ∑ r ∈ Finset.range (2 * (k + 1)), C r * 3 ^ r
  have hzero : Tendsto (fun n : ℕ => (D : ℝ) / n) atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (D : ℝ)
  rw [Metric.tendsto_atTop] at hzero
  obtain ⟨N, hN⟩ := hzero ε hε
  filter_upwards [eventually_ge_atTop N,
    eventually_ge_atTop (2 * (k + 1)), eventually_ge_atTop 1]
      with n hnN hnlarge hnpos
  intro P Q
  have hsum :
      ∑ r ∈ Finset.range (2 * (k + 1)),
          (((compatibleWitnessFamiliesBySupport P Q (k + 1) r).card *
            (n - r).factorial : ℕ) : ℝ) / n.factorial ≤
        (D : ℝ) / n := by
    calc
      _ ≤ ∑ r ∈ Finset.range (2 * (k + 1)),
          ((C r * 3 ^ r : ℕ) : ℝ) / n := by
        apply Finset.sum_le_sum
        intro r hr
        have hrlt : r < 2 * (k + 1) := Finset.mem_range.mp hr
        by_cases hrzero : r = 0
        · subst r
          rw [compatibleWitnessFamiliesBySupport_zero_eq_empty _ _ (k + 1) (by omega)]
          simp
          positivity
        · have hcount := card_compatibleWitnessFamiliesBySupport_le
              P Q (k + 1) r (by omega) hrlt
          have hcount' :
              (compatibleWitnessFamiliesBySupport P Q (k + 1) r).card ≤
                C r * n ^ (r - 1) := by
            simpa only [C, mul_assoc, mul_left_comm, mul_comm] using hcount
          exact sparse_factorial_term_le_const_div
            (compatibleWitnessFamiliesBySupport P Q (k + 1) r).card
            (C r) r n (Nat.pos_of_ne_zero hrzero) (by omega) hnpos hcount'
      _ = (D : ℝ) / n := by
        dsimp [D]
        push_cast
        rw [← Finset.sum_div]
  exact hsum.trans_lt (by
    have hd := hN n hnN
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hd
    exact hd)

private theorem eventually_uniform_overlapContribution_lt
    (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ P Q : BoundedPartition n,
      (((overlappingWitnessFamilies P Q k).card *
        (n - 2 * k).factorial : ℕ) : ℝ) / n.factorial < ε := by
  obtain rfl | k := k
  · filter_upwards with n
    intro P Q
    have hcount := card_overlappingWitnessFamilies_le_polynomial P Q 0
    have hcard : (overlappingWitnessFamilies P Q 0).card = 0 := by
      omega
    simp [hcard, hε]
  let C : ℕ := 36 * (2 * (k + 1)) ^ 2 * 9 ^ k
  let d : ℕ := 2 * (k + 1)
  have hzero : Tendsto (fun n : ℕ => ((C * 3 ^ d : ℕ) : ℝ) / n)
      atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat ((C * 3 ^ d : ℕ) : ℝ)
  rw [Metric.tendsto_atTop] at hzero
  obtain ⟨N, hN⟩ := hzero ε hε
  filter_upwards [eventually_ge_atTop N, eventually_ge_atTop d,
    eventually_ge_atTop 1] with n hnN hnd hnpos
  intro P Q
  have hcount :
      (overlappingWitnessFamilies P Q (k + 1)).card ≤
        C * n ^ (d - 1) := by
    calc
      (overlappingWitnessFamilies P Q (k + 1)).card ≤
          2 * (2 * (k + 1)) ^ 2 *
            ((9 * n ^ 2) ^ ((k + 1) - 1) * (18 * n)) :=
        card_overlappingWitnessFamilies_le_polynomial P Q (k + 1)
      _ = C * n ^ (d - 1) := by
        dsimp [C, d]
        simp only [mul_pow]
        rw [← pow_mul n 2 k, show 2 * (k + 1) - 1 = 2 * k + 1 by omega,
          pow_succ]
        ring
  have hterm := sparse_factorial_term_le_const_div
    (overlappingWitnessFamilies P Q (k + 1)).card C d n
    (by dsimp [d]; omega) hnd hnpos hcount
  exact hterm.trans_lt (by
    have hd := hN n hnN
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hd
    exact hd)

private theorem normalizedBinomialMoment_eq_top_sub_overlap_add_lower
    (P Q : BoundedPartition n) (k : ℕ) :
    normalizedBinomialMoment (collisionCount P Q) k =
      ((Fintype.card (CollisionWitness P Q)).choose k : ℝ) *
          ((n - 2 * k).factorial : ℝ) / n.factorial -
        ((overlappingWitnessFamilies P Q k).card : ℝ) *
          ((n - 2 * k).factorial : ℝ) / n.factorial +
        ∑ r ∈ Finset.range (2 * k),
          (((compatibleWitnessFamiliesBySupport P Q k r).card *
            (n - r).factorial : ℕ) : ℝ) / n.factorial := by
  rw [normalizedBinomialMoment, binomialMoment_collisionCount_eq_natCast,
    card_sym, collisionBinomialMomentNat_eq_sum_support_strata,
    Finset.sum_range_succ,
    compatibleWitnessFamiliesBySupport_two_mul_eq_disjoint]
  push_cast
  rw [add_div, Finset.sum_div]
  have hcR :
      ((disjointWitnessFamilies P Q k).card : ℝ) +
          (overlappingWitnessFamilies P Q k).card =
        (Fintype.card (CollisionWitness P Q)).choose k := by
    exact_mod_cast card_disjoint_add_card_overlapping_eq_choose P Q k
  rw [← hcR]
  ring

private theorem uniformCollisionMomentApproximation_of_top
    (htop : ∀ (k : ℕ) (ε : ℝ), 0 < ε → ∀ᶠ n : ℕ in atTop,
      ∀ W : ℕ, W ≤ 9 * n ^ 2 →
        |(W.choose k : ℝ) * ((n - 2 * k).factorial : ℝ) / n.factorial -
          ((W : ℝ) / ((n : ℝ) * (n - 1))) ^ k /
            (k.factorial : ℝ)| < ε) :
    UniformCollisionMomentApproximation := by
  intro k ε hε
  have hthird : 0 < ε / 3 := by positivity
  have htop' := htop k (ε / 3) hthird
  have hoverlap := eventually_uniform_overlapContribution_lt k hthird
  have hlower := eventually_uniform_lowerSupportContribution_lt k hthird
  filter_upwards [htop', hoverlap, hlower, eventually_ge_atTop 2]
      with n hnTop hnOverlap hnLower hn
  intro P Q
  let W := Fintype.card (CollisionWitness P Q)
  let top : ℝ := (W.choose k : ℝ) * ((n - 2 * k).factorial : ℝ) / n.factorial
  let overlap : ℝ := ((overlappingWitnessFamilies P Q k).card : ℝ) *
    ((n - 2 * k).factorial : ℝ) / n.factorial
  let lower : ℝ := ∑ r ∈ Finset.range (2 * k),
    (((compatibleWitnessFamiliesBySupport P Q k r).card *
      (n - r).factorial : ℕ) : ℝ) / n.factorial
  let ideal : ℝ := collisionMean P Q ^ k / (k.factorial : ℝ)
  have hW : W ≤ 9 * n ^ 2 := CollisionWitness.card_le_nine_mul_sq P Q
  have htopIdeal : |top - ideal| < ε / 3 := by
    have h := hnTop W hW
    have hmean : collisionMean P Q =
        (W : ℝ) / ((n : ℝ) * (n - 1)) := by
      rw [collisionMean_eq P Q hn]
      dsimp only [W]
      rw [CollisionWitness.card_eq_two_mul]
      push_cast
      ring
    dsimp only [top, ideal]
    rw [hmean]
    exact h
  have hoverlap' : overlap < ε / 3 := by
    simpa only [overlap, Nat.cast_mul] using hnOverlap P Q
  have hlower' : lower < ε / 3 := by simpa only [lower] using hnLower P Q
  have hoverlap0 : 0 ≤ overlap := by dsimp [overlap]; positivity
  have hlower0 : 0 ≤ lower := by dsimp [lower]; positivity
  have hdecomp : normalizedBinomialMoment (collisionCount P Q) k =
      top - overlap + lower := by
    simpa only [top, overlap, lower, W] using
      normalizedBinomialMoment_eq_top_sub_overlap_add_lower P Q k
  calc
    |normalizedBinomialMoment (collisionCount P Q) k - ideal| =
        |(top - ideal) + (-overlap + lower)| := by rw [hdecomp]; ring
    _ ≤ |top - ideal| + |-overlap + lower| := abs_add_le _ _
    _ ≤ |top - ideal| + (overlap + lower) := by
      gcongr
      calc
        |-overlap + lower| = |overlap - lower| := by
          rw [show -overlap + lower = -(overlap - lower) by ring, abs_neg]
        _ ≤ |overlap| + |lower| := abs_sub overlap lower
        _ = overlap + lower := by
          rw [abs_of_nonneg hoverlap0, abs_of_nonneg hlower0]
    _ < ε := by linarith

/-- Uniform fixed-order binomial-moment approximation for every pair of
block-size-at-most-four partitions. -/
theorem uniformCollisionMomentApproximation :
    UniformCollisionMomentApproximation :=
  uniformCollisionMomentApproximation_of_top
    eventually_uniform_top_support_term

/-- For bounded Young subgroups, a successful conjugator is exactly a simple incidence table. -/
theorem successProbability_youngSubgroup_eq_simpleConfigurationFraction
    (P Q : BoundedPartition n) :
    successProbability (youngSubgroup P) (youngSubgroup Q) =
      simpleConfigurationFraction P Q := by
  classical
  unfold successProbability simpleConfigurationFraction goodConjugators
  have hfilter :
      (Finset.univ.filter fun sigma : Sym n =>
          Disjoint (youngSubgroup P) (conjugate (youngSubgroup Q) sigma)) =
        Finset.univ.filter fun sigma : Sym n => IsSimple P Q sigma := by
    ext sigma
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact disjoint_youngSubgroup_conjugate_iff_isSimple P Q sigma
  rw [hfilter]

/-- Equivalent zero-count form of the Young-subgroup success probability. -/
theorem successProbability_youngSubgroup_eq_normalizedZeroCount
    (P Q : BoundedPartition n) :
    successProbability (youngSubgroup P) (youngSubgroup Q) =
      normalizedZeroCount (collisionCount P Q) := by
  rw [successProbability_youngSubgroup_eq_simpleConfigurationFraction,
    simpleConfigurationFraction_eq_normalizedZeroCount]

/-- Specialized identity for the consecutive four-block family. -/
theorem successProbability_fourBlock_eq_simpleConfigurationFraction (n : ℕ) :
    successProbability (fourBlockSolubleSubgroup n).carrier
        (fourBlockSolubleSubgroup n).carrier =
      simpleConfigurationFraction (fourBlockPartition n) (fourBlockPartition n) := by
  exact successProbability_youngSubgroup_eq_simpleConfigurationFraction _ _

/-- Specialized zero-collision identity for the consecutive four-block family. -/
theorem successProbability_fourBlock_eq_normalizedZeroCount (n : ℕ) :
    successProbability (fourBlockSolubleSubgroup n).carrier
        (fourBlockSolubleSubgroup n).carrier =
      normalizedZeroCount
        (collisionCount (fourBlockPartition n) (fourBlockPartition n)) := by
  exact successProbability_youngSubgroup_eq_normalizedZeroCount _ _

/-- Pointwise upper bound for the worst soluble-subgroup probability by the explicit witness. -/
theorem worstProbability_le_fourBlockSimpleConfigurationFraction (n : ℕ) :
    worstProbability n ≤
      simpleConfigurationFraction (fourBlockPartition n) (fourBlockPartition n) := by
  calc
    worstProbability n ≤ successProbability (fourBlockSolubleSubgroup n).carrier
        (fourBlockSolubleSubgroup n).carrier :=
      worstProbability_le_successProbability _ _
    _ = simpleConfigurationFraction (fourBlockPartition n) (fourBlockPartition n) :=
      successProbability_fourBlock_eq_simpleConfigurationFraction n

/-- The number of collision witnesses divided by `n²`. -/
noncomputable def fourBlockWitnessDensity (n : ℕ) : ℝ :=
  Fintype.card (CollisionWitness (fourBlockPartition n) (fourBlockPartition n)) / (n : ℝ) ^ 2

/-- The witness density for consecutive four-blocks tends to `9/2`. -/
theorem tendsto_fourBlockWitnessDensity :
    Tendsto fourBlockWitnessDensity atTop (nhds (9 / 2 : ℝ)) := by
  have hmain : Tendsto (fun n : ℕ => 2 * fourBlockPairDensity n ^ 2) atTop
      (nhds (9 / 2 : ℝ)) := by
    convert tendsto_const_nhds.mul (tendsto_fourBlockPairDensity.pow 2) using 1 <;> norm_num
  apply hmain.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  rw [fourBlockWitnessDensity, CollisionWitness.card_eq_two_mul, fourBlockPairDensity]
  push_cast
  field_simp

/-- The exact collision mean for consecutive four-blocks tends to `9/2`. -/
theorem tendsto_fourBlockCollisionMean :
    Tendsto (fun n => collisionMean (fourBlockPartition n) (fourBlockPartition n))
      atTop (nhds (9 / 2 : ℝ)) := by
  have hratio : Tendsto (fun n : ℕ => (n : ℝ) / (n - 1 : ℝ)) atTop (nhds 1) := by
    simpa [sub_eq_add_neg] using tendsto_natCast_div_add_atTop (-1 : ℝ)
  have hmain : Tendsto
      (fun n : ℕ => 2 * fourBlockPairDensity n ^ 2 * ((n : ℝ) / (n - 1 : ℝ)))
      atTop (nhds (9 / 2 : ℝ)) := by
    convert (tendsto_const_nhds.mul (tendsto_fourBlockPairDensity.pow 2)).mul hratio
      using 1 <;> norm_num
  apply hmain.congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  rw [collisionMean_eq _ _ hn, fourBlockPairDensity]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hn1 : (n : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
    linarith
  field_simp

/-- The normalized first binomial moment has the required Poisson parameter. -/
theorem tendsto_fourBlockNormalizedBinomialMoment_one :
    Tendsto
      (fun n => normalizedBinomialMoment
        (collisionCount (fourBlockPartition n) (fourBlockPartition n)) 1)
      atTop (nhds (9 / 2 : ℝ)) := by
  simpa only [normalizedBinomialMoment_one_eq_collisionMean] using
    tendsto_fourBlockCollisionMean

/-- Every fixed normalized collision binomial moment for consecutive four-blocks
has its Poisson limit. -/
theorem tendsto_fourBlockNormalizedBinomialMoment (k : ℕ) :
    Tendsto
      (fun n => normalizedBinomialMoment
        (collisionCount (fourBlockPartition n) (fourBlockPartition n)) k)
      atTop (nhds ((9 / 2 : ℝ) ^ k / (k.factorial : ℝ))) := by
  let C : ℕ → ℕ := fun r =>
    (r + 1) ^ 2 * (((r * 4) ^ (2 * k)) ^ 2)
  apply tendsto_normalizedBinomialMoment_of_support_bound
    fourBlockPartition fourBlockPartition (9 / 2 : ℝ) (by norm_num)
    (by
      change Tendsto fourBlockWitnessDensity atTop (nhds (9 / 2 : ℝ))
      exact tendsto_fourBlockWitnessDensity)
    k C
  intro r hr
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hcount := card_compatibleWitnessFamiliesBySupport_le
    (fourBlockPartition n) (fourBlockPartition n) k r (by omega) hr
  simpa only [C, mul_assoc, mul_left_comm, mul_comm] using hcount

/-- Once all collision binomial moments have their Poisson limits, the explicit soluble
four-block witness has success probability tending to `exp (-9/2)`. -/
theorem tendsto_fourBlockSuccessProbability_of_binomialMoments
    (hmoment : ∀ j : ℕ,
      Tendsto
        (fun n => normalizedBinomialMoment
          (collisionCount (fourBlockPartition n) (fourBlockPartition n)) j)
        atTop (nhds ((9 / 2 : ℝ) ^ j / (j.factorial : ℝ)))) :
    Tendsto
      (fun n => successProbability (fourBlockSolubleSubgroup n).carrier
        (fourBlockSolubleSubgroup n).carrier)
      atTop (nhds (Real.exp (-(9 / 2 : ℝ)))) := by
  have hs := tendsto_simpleConfigurationFraction_of_binomialMoments
    fourBlockPartition fourBlockPartition (9 / 2 : ℝ) hmoment
  exact hs.congr' (Eventually.of_forall fun n =>
    (successProbability_fourBlock_eq_simpleConfigurationFraction n).symm)

/-- The success probability of the explicit soluble four-block witness tends to
`exp (-9/2)`. -/
theorem tendsto_fourBlockSuccessProbability :
    Tendsto
      (fun n => successProbability (fourBlockSolubleSubgroup n).carrier
        (fourBlockSolubleSubgroup n).carrier)
      atTop (nhds (Real.exp (-(9 / 2 : ℝ)))) :=
  tendsto_fourBlockSuccessProbability_of_binomialMoments
    tendsto_fourBlockNormalizedBinomialMoment

/-- The explicit witness gives the required eventual upper estimate for the infimum. -/
theorem eventually_worstProbability_lt_exp_neg_nine_halves_add_of_binomialMoments
    (hmoment : ∀ j : ℕ,
      Tendsto
        (fun n => normalizedBinomialMoment
          (collisionCount (fourBlockPartition n) (fourBlockPartition n)) j)
        atTop (nhds ((9 / 2 : ℝ) ^ j / (j.factorial : ℝ))))
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ n : ℕ in atTop,
      worstProbability n < Real.exp (-(9 / 2 : ℝ)) + epsilon := by
  have hs := tendsto_fourBlockSuccessProbability_of_binomialMoments hmoment
  have hlim : Real.exp (-(9 / 2 : ℝ)) < Real.exp (-(9 / 2 : ℝ)) + epsilon :=
    lt_add_of_pos_right _ hepsilon
  filter_upwards [hs.eventually (Iio_mem_nhds hlim)] with n hn
  exact (worstProbability_le_successProbability
    (fourBlockSolubleSubgroup n) (fourBlockSolubleSubgroup n)).trans_lt hn

/-- The explicit four-block witness gives the unconditional eventual upper estimate. -/
theorem eventually_worstProbability_lt_exp_neg_nine_halves_add
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ n : ℕ in atTop,
      worstProbability n < Real.exp (-(9 / 2 : ℝ)) + epsilon :=
  eventually_worstProbability_lt_exp_neg_nine_halves_add_of_binomialMoments
    tendsto_fourBlockNormalizedBinomialMoment hepsilon

/-- Limsup form of the upper bound supplied by the explicit soluble witness. -/
theorem limsup_worstProbability_le_exp_neg_nine_halves_of_binomialMoments
    (hmoment : ∀ j : ℕ,
      Tendsto
        (fun n => normalizedBinomialMoment
          (collisionCount (fourBlockPartition n) (fourBlockPartition n)) j)
        atTop (nhds ((9 / 2 : ℝ) ^ j / (j.factorial : ℝ)))) :
    limsup worstProbability atTop ≤ Real.exp (-(9 / 2 : ℝ)) := by
  have hs := tendsto_fourBlockSuccessProbability_of_binomialMoments hmoment
  have hpoint : ∀ᶠ n : ℕ in atTop,
      worstProbability n ≤ successProbability (fourBlockSolubleSubgroup n).carrier
        (fourBlockSolubleSubgroup n).carrier :=
    Eventually.of_forall fun n => worstProbability_le_successProbability
      (fourBlockSolubleSubgroup n) (fourBlockSolubleSubgroup n)
  calc
    limsup worstProbability atTop ≤
        limsup (fun n => successProbability (fourBlockSolubleSubgroup n).carrier
          (fourBlockSolubleSubgroup n).carrier) atTop :=
      limsup_le_limsup hpoint
        (isCoboundedUnder_le_of_le atTop worstProbability_nonneg)
        hs.isBoundedUnder_le
    _ = Real.exp (-(9 / 2 : ℝ)) := hs.limsup_eq

/-- Unconditional limsup upper bound supplied by the explicit soluble witness. -/
theorem limsup_worstProbability_le_exp_neg_nine_halves :
    limsup worstProbability atTop ≤ Real.exp (-(9 / 2 : ℝ)) :=
  limsup_worstProbability_le_exp_neg_nine_halves_of_binomialMoments
    tendsto_fourBlockNormalizedBinomialMoment

end Kourovka213
