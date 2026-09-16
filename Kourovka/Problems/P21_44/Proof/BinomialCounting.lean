import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Entropy bound for finite sets of sign-change positions

The proof assigns each subset its Bernoulli weight. The total weight of all
subsets is one, while every subset with at most `δ * n` elements has weight at
least `exp (-n * binEntropy δ)`.
-/

open scoped BigOperators

namespace Kourovka.P21_44

/-- The Bernoulli weights of all subsets of an `n`-element set sum to one. -/
theorem sum_subset_bernoulli_weights (n : ℕ) (δ : ℝ) :
    (∑ s : Finset (Fin n), δ ^ s.card * (1 - δ) ^ sᶜ.card) = 1 := by
  simpa only [add_sub_cancel, Finset.prod_const_one, Finset.prod_const] using
    (Fintype.prod_add (fun _ : Fin n => δ) (fun _ => 1 - δ)).symm

/-- Every subset below the mean has at least the entropy threshold weight. -/
theorem entropy_threshold_le_subset_weight {n : ℕ} {δ : ℝ}
    (hδ : 0 < δ) (hδhalf : δ < 1 / 2) (s : Finset (Fin n))
    (hsize : (s.card : ℝ) ≤ δ * n) :
    Real.exp (-(n : ℝ) * Real.binEntropy δ) ≤
      δ ^ s.card * (1 - δ) ^ sᶜ.card := by
  have hcomp : 0 < 1 - δ := by linarith
  have hw : 0 < δ ^ s.card * (1 - δ) ^ sᶜ.card := by positivity
  have hlogs : Real.log δ ≤ Real.log (1 - δ) :=
    Real.log_le_log hδ (by linarith)
  have hcard : (s.card : ℝ) + (sᶜ.card : ℝ) = n := by
    exact_mod_cast (show s.card + sᶜ.card = n by
      simpa only [Fintype.card_fin] using Finset.card_add_card_compl s)
  rw [← Real.exp_log hw]
  apply Real.exp_le_exp.2
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  rw [Real.binEntropy, Real.log_inv, Real.log_inv]
  rw [show (sᶜ.card : ℝ) = n - s.card by linarith]
  nlinarith [mul_nonneg (sub_nonneg.2 hsize) (sub_nonneg.2 hlogs)]

/-- The number of subsets with at most `δ * n` elements is at most
`exp (n * binEntropy δ)`. -/
theorem card_small_subsets_le_entropy (n : ℕ) {δ : ℝ}
    (hδ : 0 < δ) (hδhalf : δ < 1 / 2) :
    ((Finset.univ.filter (fun s : Finset (Fin n) => (s.card : ℝ) ≤ δ * n)).card : ℝ)
      ≤ Real.exp ((n : ℝ) * Real.binEntropy δ) := by
  classical
  have hcomp : 0 < 1 - δ := by linarith
  let small := Finset.univ.filter (fun s : Finset (Fin n) => (s.card : ℝ) ≤ δ * n)
  have hweights : (small.card : ℝ) * Real.exp (-(n : ℝ) * Real.binEntropy δ) ≤ 1 := by
    calc
      _ = ∑ _s ∈ small, Real.exp (-(n : ℝ) * Real.binEntropy δ) := by simp
      _ ≤ ∑ s ∈ small, δ ^ s.card * (1 - δ) ^ sᶜ.card := by
        apply Finset.sum_le_sum
        intro s hs
        exact entropy_threshold_le_subset_weight hδ hδhalf s (Finset.mem_filter.1 hs).2
      _ ≤ ∑ s : Finset (Fin n), δ ^ s.card * (1 - δ) ^ sᶜ.card := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        intro s _ _
        positivity
      _ = 1 := sum_subset_bernoulli_weights n δ
  have hcancel : Real.exp (-(n : ℝ) * Real.binEntropy δ) *
      Real.exp ((n : ℝ) * Real.binEntropy δ) = 1 := by
    rw [← Real.exp_add]
    simp only [neg_mul, neg_add_cancel, Real.exp_zero]
  have hmul := mul_le_mul_of_nonneg_right hweights
    (Real.exp_pos ((n : ℝ) * Real.binEntropy δ)).le
  simpa only [mul_assoc, hcancel, mul_one, one_mul] using hmul

/-- Subtype-cardinality version of the entropy estimate. -/
theorem fintype_card_small_subsets_le_entropy (n : ℕ) {δ : ℝ}
    (hδ : 0 < δ) (hδhalf : δ < 1 / 2) :
    (Fintype.card {s : Finset (Fin n) // (s.card : ℝ) ≤ δ * n} : ℝ)
      ≤ Real.exp ((n : ℝ) * Real.binEntropy δ) := by
  classical
  simpa only [Fintype.card_subtype] using card_small_subsets_le_entropy n hδ hδhalf

/-- The subset count is the usual lower binomial tail. -/
theorem card_small_subsets_eq_binomial_sum (n : ℕ) (δ : ℝ) :
    (Finset.univ.filter (fun s : Finset (Fin n) => (s.card : ℝ) ≤ δ * n)).card =
      ∑ j ∈ (Finset.range (n + 1)).filter (fun j : ℕ => (j : ℝ) ≤ δ * n), n.choose j := by
  classical
  calc
    _ = ∑ s ∈ (Finset.univ : Finset (Fin n)).powerset,
        if (s.card : ℝ) ≤ δ * n then 1 else 0 := by
      simp only [Finset.powerset_univ, Finset.card_filter]
    _ = ∑ j ∈ Finset.range (n + 1),
        ∑ s ∈ (Finset.univ : Finset (Fin n)).powersetCard j,
          if (s.card : ℝ) ≤ δ * n then 1 else 0 := by
      simpa only [Finset.card_univ, Fintype.card_fin] using
        Finset.sum_powerset (Finset.univ : Finset (Fin n))
          (fun s => if (s.card : ℝ) ≤ δ * n then (1 : ℕ) else 0)
    _ = _ := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_powersetCard j (Finset.univ : Finset (Fin n))
        (fun k : ℕ => if (k : ℝ) ≤ δ * n then (1 : ℕ) else 0)]
      simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        mul_ite, mul_one, mul_zero, Nat.cast_id]

/-- Binomial-sum version, with a real threshold avoiding floor conventions. -/
theorem binomial_sum_le_entropy (n : ℕ) {δ : ℝ}
    (hδ : 0 < δ) (hδhalf : δ < 1 / 2) :
    ((∑ j ∈ (Finset.range (n + 1)).filter (fun j : ℕ => (j : ℝ) ≤ δ * n),
      n.choose j : ℕ) : ℝ) ≤ Real.exp ((n : ℝ) * Real.binEntropy δ) := by
  rw [← card_small_subsets_eq_binomial_sum]
  exact card_small_subsets_le_entropy n hδ hδhalf

/-- Counting an injective encoding by a length, three bits, and a sparse subset.
The three bits are presented as `Fin 8`; no realizability of all codes is needed. -/
theorem card_le_entropy_of_injective_encoding {α : Type*} [Fintype α]
    (n : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (code : α → Fin (n + 1) × Fin 8 ×
      {s : Finset (Fin n) // (s.card : ℝ) ≤ δ * n})
    (hcode : Function.Injective code) :
    (Fintype.card α : ℝ) ≤ 8 * ((n : ℝ) + 1) *
      Real.exp ((n : ℝ) * Real.binEntropy δ) := by
  classical
  have hc := Fintype.card_le_of_injective code hcode
  have hcr : (Fintype.card α : ℝ) ≤ ((n : ℝ) + 1) * (8 *
      (Fintype.card {s : Finset (Fin n) // (s.card : ℝ) ≤ δ * n} : ℝ)) := by
    exact_mod_cast (by simpa only [Fintype.card_prod, Fintype.card_fin] using hc)
  calc
    (Fintype.card α : ℝ) ≤ _ := hcr
    _ ≤ ((n : ℝ) + 1) * (8 * Real.exp ((n : ℝ) * Real.binEntropy δ)) := by
      gcongr
      exact fintype_card_small_subsets_le_entropy n hδ hδhalf
    _ = _ := by ring

end Kourovka.P21_44
