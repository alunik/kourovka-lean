import Kourovka.Problems.P21_03.Proof.FactorialRatioBound
import Kourovka.Problems.P21_03.Proof.NoncoreReduction
import Kourovka.Problems.P21_03.Proof.SupportSeries

/-!
# From forest support counts to a vanishing non-core error

This module is the numerical interface between the recursive group argument and the
finite conjugation union bound.  Its main theorem says that the two cleared-denominator
support estimates imply a uniform error bounded by a fixed summable series divided by
the degree.
-/

open Filter
open scoped BigOperators Topology

namespace Kourovka213

/-- The two support estimates required for one soluble permutation subgroup. -/
def SupportBoundsFor (C : ℕ) {n : ℕ} (H : SolubleSubgroup n) : Prop :=
  ∀ s : ℕ,
    (supportSlice H.carrier s).card * s ^ (s / 2) ≤
        C ^ s * n ^ (s / 2) ∧
      (outsideCoreSlice H.carrier s).card * s ^ ((s - 1) / 2) ≤
        C ^ s * n ^ ((s - 1) / 2)

/-- Uniform support estimates for every soluble subgroup.  The final proof only
needs these estimates for a soluble forest envelope containing each given subgroup;
the stronger formulation remains a convenient reusable interface. -/
def UniformSupportBounds (C : ℕ) : Prop :=
  ∀ (n : ℕ) (H : SolubleSubgroup n), SupportBoundsFor C H

/-- The fixed summable majorant, truncated at the current degree and divided by `n`. -/
noncomputable def noncoreErrorBound (C n : ℕ) : ℝ :=
  2 * (∑ s ∈ Finset.range (n + 1), supportSeriesTerm (3 * C * C) s) / n

theorem support_count_product_bound
    (A B C n s : ℕ)
    (hA : A * s ^ ((s - 1) / 2) ≤ C ^ s * n ^ ((s - 1) / 2))
    (hB : B * s ^ (s / 2) ≤ C ^ s * n ^ (s / 2)) :
    A * B * s ^ (s - 1) ≤ (C * C) ^ s * n ^ (s - 1) := by
  have hmul := Nat.mul_le_mul hA hB
  have hsum : (s - 1) / 2 + s / 2 = s - 1 := by omega
  have hsPow : s ^ ((s - 1) / 2) * s ^ (s / 2) = s ^ (s - 1) := by
    rw [← pow_add, hsum]
  have hnPow : n ^ ((s - 1) / 2) * n ^ (s / 2) = n ^ (s - 1) := by
    rw [← pow_add, hsum]
  have hCPow : C ^ s * C ^ s = (C * C) ^ s := by rw [Nat.mul_pow]
  calc
    A * B * s ^ (s - 1) =
        (A * s ^ ((s - 1) / 2)) * (B * s ^ (s / 2)) := by
      rw [← hsPow]
      ac_rfl
    _ ≤ (C ^ s * n ^ ((s - 1) / 2)) * (C ^ s * n ^ (s / 2)) := hmul
    _ = (C * C) ^ s * n ^ (s - 1) := by
      rw [← hCPow, ← hnPow]
      ac_rfl

/-- Cleared-denominator form of the bound for one support slice. -/
theorem support_term_arithmetic_bound
    (A B C n s : ℕ) (hs : 1 ≤ s) (hsn : s ≤ n)
    (hA : A * s ^ ((s - 1) / 2) ≤ C ^ s * n ^ ((s - 1) / 2))
    (hB : B * s ^ (s / 2) ≤ C ^ s * n ^ (s / 2)) :
    n * (A * B * ((n - s).factorial * s ^ (s / 2))) * s ^ ((s - 1) / 2) ≤
      (3 * C * C) ^ s * n.factorial := by
  have hcounts := support_count_product_bound A B C n s hA hB
  have hsum : s / 2 + (s - 1) / 2 = s - 1 := by omega
  have hsPow : s ^ (s / 2) * s ^ ((s - 1) / 2) = s ^ (s - 1) := by
    rw [← pow_add, hsum]
  have hnSucc : n * n ^ (s - 1) = n ^ s := by
    calc
      n * n ^ (s - 1) = n ^ (s - 1) * n := Nat.mul_comm _ _
      _ = n ^ ((s - 1) + 1) := (pow_succ n (s - 1)).symm
      _ = n ^ s := by congr 1 <;> omega
  calc
    n * (A * B * ((n - s).factorial * s ^ (s / 2))) * s ^ ((s - 1) / 2) =
        (A * B * s ^ (s - 1)) * (n * (n - s).factorial) := by
      rw [← hsPow]
      ac_rfl
    _ ≤ ((C * C) ^ s * n ^ (s - 1)) * (n * (n - s).factorial) :=
      Nat.mul_le_mul_right _ hcounts
    _ = (C * C) ^ s * (n ^ s * (n - s).factorial) := by
      rw [← hnSucc]
      ac_rfl
    _ ≤ (C * C) ^ s * (3 ^ s * n.factorial) :=
      Nat.mul_le_mul_left _ (pow_mul_factorial_sub_le_three_pow_mul_factorial n s hsn)
    _ = (3 * C * C) ^ s * n.factorial := by
      simp only [Nat.mul_pow]
      ring

private theorem source_support_le_degree {n s : ℕ} {H : Subgroup (Sym n)}
    (h : (outsideCoreSlice H s).Nonempty) : s ≤ n := by
  obtain ⟨g, hg⟩ := h
  have hcard := g.support.card_le_univ
  simpa [(mem_outsideCoreSlice.mp hg).2.1] using hcard

private theorem supportTerm_div_factorial_le
    (A B C n s : ℕ) (hn : 0 < n) (hs : 1 ≤ s) (hsn : s ≤ n)
    (hA : A * s ^ ((s - 1) / 2) ≤ C ^ s * n ^ ((s - 1) / 2))
    (hB : B * s ^ (s / 2) ≤ C ^ s * n ^ (s / 2)) :
    ((A * B * ((n - s).factorial * s ^ (s / 2)) : ℕ) : ℝ) / n.factorial ≤
      supportSeriesTerm (3 * C * C) s / n := by
  have hnat := support_term_arithmetic_bound A B C n s hs hsn hA hB
  have hreal :
      (n : ℝ) * (A * B * ((n - s).factorial * s ^ (s / 2)) : ℕ) *
          (s : ℝ) ^ ((s - 1) / 2) ≤
        (3 * C * C : ℕ) ^ s * (n.factorial : ℕ) := by
    exact_mod_cast hnat
  rw [supportSeriesTerm, div_div]
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < n.factorial)
    (mul_pos (by positivity) (by exact_mod_cast hn))).2
  simpa [Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat, mul_assoc, mul_left_comm, mul_comm]
    using hreal

/-- The exact non-core probability is bounded by `noncoreErrorBound`. -/
theorem extraBadProbability_le_noncoreErrorBound
    {C : ℕ} (H K : SolubleSubgroup n)
    (hH : SupportBoundsFor C H) (hK : SupportBoundsFor C K) :
    extraBadProbability H K ≤ noncoreErrorBound C n := by
  by_cases hn : n = 0
  · subst n
    simp [extraBadProbability, extraBadConjugators, noncoreErrorBound]
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  let termHK : ℕ → ℕ := fun s =>
    (outsideCoreSlice H.carrier s).card * (supportSlice K.carrier s).card *
      ((n - s).factorial * s ^ (s / 2))
  let termKH : ℕ → ℕ := fun s =>
    (supportSlice H.carrier s).card * (outsideCoreSlice K.carrier s).card *
      ((n - s).factorial * s ^ (s / 2))
  have hcard := card_extraBadConjugators_le_support_products H K
  have hcast : ((extraBadConjugators H K).card : ℝ) ≤
      (∑ s ∈ Finset.range (n + 1), (termHK s : ℝ)) +
        ∑ s ∈ Finset.range (n + 1), (termKH s : ℝ) := by
    exact_mod_cast hcard
  have htermHK : ∀ s ∈ Finset.range (n + 1),
      (termHK s : ℝ) / n.factorial ≤ supportSeriesTerm (3 * C * C) s / n := by
    intro s _hsrange
    by_cases hzero : (outsideCoreSlice H.carrier s).card = 0
    · simp only [termHK, hzero, zero_mul, Nat.cast_zero, zero_div]
      exact div_nonneg
        (div_nonneg (by positivity) (by positivity)) (by exact_mod_cast hnpos.le)
    · have hnon : (outsideCoreSlice H.carrier s).Nonempty :=
        Finset.card_pos.mp (Nat.pos_of_ne_zero hzero)
      exact supportTerm_div_factorial_le _ _ C n s hnpos
        (three_le_of_outsideCoreSlice_nonempty H.carrier s hnon |>.trans' (by omega))
        (source_support_le_degree hnon)
        (hH s).2 (hK s).1
  have htermKH : ∀ s ∈ Finset.range (n + 1),
      (termKH s : ℝ) / n.factorial ≤ supportSeriesTerm (3 * C * C) s / n := by
    intro s _hsrange
    by_cases hzero : (outsideCoreSlice K.carrier s).card = 0
    · simp only [termKH, hzero, mul_zero, zero_mul, Nat.cast_zero, zero_div]
      exact div_nonneg
        (div_nonneg (by positivity) (by positivity)) (by exact_mod_cast hnpos.le)
    · have hnon : (outsideCoreSlice K.carrier s).Nonempty :=
        Finset.card_pos.mp (Nat.pos_of_ne_zero hzero)
      simpa [termKH, mul_assoc, mul_left_comm, mul_comm] using
        (supportTerm_div_factorial_le
          (outsideCoreSlice K.carrier s).card (supportSlice H.carrier s).card
          C n s hnpos
          (three_le_of_outsideCoreSlice_nonempty K.carrier s hnon |>.trans' (by omega))
          (source_support_le_degree hnon)
          (hK s).2 (hH s).1)
  calc
    extraBadProbability H K = ((extraBadConjugators H K).card : ℝ) / n.factorial := by
      simp [extraBadProbability, card_sym]
    _ ≤ ((∑ s ∈ Finset.range (n + 1), (termHK s : ℝ)) +
          ∑ s ∈ Finset.range (n + 1), (termKH s : ℝ)) / n.factorial :=
      div_le_div_of_nonneg_right hcast (by positivity)
    _ = (∑ s ∈ Finset.range (n + 1), (termHK s : ℝ) / n.factorial) +
          ∑ s ∈ Finset.range (n + 1), (termKH s : ℝ) / n.factorial := by
      rw [add_div, Finset.sum_div, Finset.sum_div]
    _ ≤ (∑ s ∈ Finset.range (n + 1), supportSeriesTerm (3 * C * C) s / n) +
          ∑ s ∈ Finset.range (n + 1), supportSeriesTerm (3 * C * C) s / n := by
      exact add_le_add (Finset.sum_le_sum htermHK) (Finset.sum_le_sum htermKH)
    _ = noncoreErrorBound C n := by
      simp only [← Finset.sum_div]
      unfold noncoreErrorBound
      ring

/-- Uniform support estimates specialize to the pointwise form used by the
non-core union bound. -/
theorem extraBadProbability_le_noncoreErrorBound_of_uniform
    {C : ℕ} (hC : UniformSupportBounds C)
    (H K : SolubleSubgroup n) :
  extraBadProbability H K ≤ noncoreErrorBound C n :=
  extraBadProbability_le_noncoreErrorBound H K (hC n H) (hC n K)

theorem noncoreErrorBound_nonneg (C n : ℕ) : 0 ≤ noncoreErrorBound C n := by
  unfold noncoreErrorBound
  apply div_nonneg
  · apply mul_nonneg (by norm_num)
    apply Finset.sum_nonneg
    intro s _hs
    unfold supportSeriesTerm
    positivity
  · exact_mod_cast Nat.zero_le n

/-- The uniform non-core error tends to zero. -/
theorem tendsto_noncoreErrorBound_zero (C : ℕ) :
    Tendsto (noncoreErrorBound C) atTop (nhds 0) := by
  let S : ℝ := ∑' s : ℕ, supportSeriesTerm (3 * C * C) s
  have hsum (n : ℕ) :
      (∑ s ∈ Finset.range (n + 1), supportSeriesTerm (3 * C * C) s) ≤ S := by
    exact (summable_supportSeriesTerm (3 * C * C)).sum_le_tsum _
      (fun i _hi => by unfold supportSeriesTerm; positivity)
  apply squeeze_zero (noncoreErrorBound_nonneg C)
    (fun n => ?_) (tendsto_const_div_atTop_nhds_zero_nat (2 * S))
  unfold noncoreErrorBound
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hsum n) (by positivity))
    (by positivity)

end Kourovka213
