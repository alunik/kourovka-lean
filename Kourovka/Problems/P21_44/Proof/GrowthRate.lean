import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic

/-!
# The numerical growth argument for Kourovka 21.44

This module isolates the analytic consequence of the section-counting recurrence.
It uses the infimum of positive exponential-envelope rates, avoiding any assumed
existence of a growth-rate limit. All recurrence hypotheses are explicit.
-/

open Filter
open scoped Topology

namespace Kourovka.P21_44

/-- A uniform exponential bound, allowing a multiplicative constant. -/
def HasExponentialEnvelope (γ : ℕ → ℝ) (s : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, γ n ≤ C * Real.exp (s * n)

/-- Polynomial factors can be absorbed into an arbitrarily small increase in rate. -/
theorem eventually_polynomial_mul_exp_le (C : ℝ) (k : ℕ) {a b : ℝ}
    (hab : a < b) :
    ∀ᶠ n : ℕ in atTop,
      C * (n : ℝ) ^ k * Real.exp (a * n) ≤ Real.exp (b * n) := by
  have h := ((isLittleO_exp_mul_rpow_of_lt (k : ℝ) hab).const_mul_left C).comp_tendsto (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [h.bound (by norm_num : (0 : ℝ) < 1)] with n hn
  simp only [Function.comp_apply, Real.rpow_natCast, one_mul, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)] at hn
  exact (le_abs_self _).trans (by simpa [mul_assoc, mul_comm, mul_left_comm] using hn)

/-- A shifted polynomial has the same absorption property. -/
theorem eventually_shifted_polynomial_mul_exp_le (C : ℝ) (hC : 0 ≤ C)
    (k : ℕ) {a b : ℝ} (hab : a < b) :
    ∀ᶠ n : ℕ in atTop,
      C * ((n : ℝ) + 2) ^ k * Real.exp (a * n) ≤ Real.exp (b * n) := by
  filter_upwards [eventually_polynomial_mul_exp_le (C * 3 ^ k) k hab,
    eventually_ge_atTop 1] with n hn hn1
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hshift : (n : ℝ) + 2 ≤ 3 * n := by linarith
  calc
    C * ((n : ℝ) + 2) ^ k * Real.exp (a * n)
        ≤ C * (3 * (n : ℝ)) ^ k * Real.exp (a * n) := by gcongr
    _ = (C * 3 ^ k) * (n : ℝ) ^ k * Real.exp (a * n) := by ring
    _ ≤ Real.exp (b * n) := hn

/-- A bound valid after finitely many indices can be made uniform by a constant. -/
theorem hasExponentialEnvelope_of_eventually {γ : ℕ → ℝ} {s : ℝ}
    (h : ∀ᶠ n : ℕ in atTop, γ n ≤ Real.exp (s * n)) :
    HasExponentialEnvelope γ s := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 h
  let C : ℝ := 1 + ∑ i ∈ Finset.range N, |γ i| / Real.exp (s * i)
  have hsum : 0 ≤ ∑ i ∈ Finset.range N, |γ i| / Real.exp (s * i) := by
    exact Finset.sum_nonneg fun i _ => div_nonneg (abs_nonneg _) (Real.exp_pos _).le
  have hC : 1 ≤ C := by dsimp [C]; linarith
  refine ⟨C, lt_of_lt_of_le zero_lt_one hC, fun n => ?_⟩
  by_cases hn : N ≤ n
  · exact (hN n hn).trans (by nlinarith [Real.exp_pos (s * n)])
  · have hnN : n ∈ Finset.range N := Finset.mem_range.2 (Nat.lt_of_not_ge hn)
    have hsingle : |γ n| / Real.exp (s * n) ≤
        ∑ i ∈ Finset.range N, |γ i| / Real.exp (s * i) :=
      Finset.single_le_sum (fun i (_ : i ∈ Finset.range N) =>
        div_nonneg (abs_nonneg (γ i)) (Real.exp_pos (s * i)).le) hnN
    have hr : |γ n| / Real.exp (s * n) ≤ C := by dsimp [C]; linarith
    exact (le_abs_self _).trans ((div_le_iff₀ (Real.exp_pos _)).1 hr)

/-- A uniform envelope yields the exact eventual bound at every larger rate. -/
theorem HasExponentialEnvelope.eventually_le {γ : ℕ → ℝ} {s t : ℝ}
    (h : HasExponentialEnvelope γ s) (hst : s < t) :
    ∀ᶠ n : ℕ in atTop, γ n ≤ Real.exp (t * n) := by
  obtain ⟨C, _, hC⟩ := h
  filter_upwards [eventually_polynomial_mul_exp_le C 0 hst] with n hn
  exact (hC n).trans (by simpa using hn)

/-- The counting recurrence after bounding each of the five sections by an envelope.
The additive one in the section budget is retained explicitly. -/
def EnvelopeRecurrence (γ : ℕ → ℝ) (h : ℝ → ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → δ < 1 / 2 →
  ∀ s : ℝ, 0 < s → ∀ C : ℝ, 0 < C →
    (∀ n : ℕ, γ n ≤ C * Real.exp (s * n)) →
    ∀ n : ℕ, γ n ≤
      8 * ((n : ℝ) + 1) * Real.exp (h δ * n) +
      60 * ((n : ℝ) + 2) ^ 5 * C ^ 5 *
        Real.exp (s * ((1 - δ / 10) * n + 1))

/-- The recurrence improves every available exponential rate. -/
theorem envelope_recurrence_improves {γ : ℕ → ℝ} {h : ℝ → ℝ}
    (hrec : EnvelopeRecurrence γ h) {δ s t : ℝ}
    (hδ : 0 < δ) (hδhalf : δ < 1 / 2) (hs : 0 < s)
    (henv : HasExponentialEnvelope γ s)
    (hht : h δ < t) (hqst : (1 - δ / 10) * s < t) :
    HasExponentialEnvelope γ t := by
  obtain ⟨C, hC, henvC⟩ := henv
  obtain ⟨v, hv, hvt⟩ := exists_between (max_lt hht hqst)
  have hhv : h δ < v := lt_of_le_of_lt (le_max_left _ _) hv
  have hqsv : (1 - δ / 10) * s < v := lt_of_le_of_lt (le_max_right _ _) hv
  apply hasExponentialEnvelope_of_eventually
  have hfirst := eventually_shifted_polynomial_mul_exp_le 8 (by norm_num) 1 hhv
  have hsecond := eventually_shifted_polynomial_mul_exp_le
    (60 * C ^ 5 * Real.exp s) (by positivity) 5 hqsv
  have hlast := eventually_polynomial_mul_exp_le 2 0 hvt
  filter_upwards [hfirst, hsecond, hlast] with n hn₁ hn₂ hn₃
  have hsmall : 8 * ((n : ℝ) + 1) * Real.exp (h δ * n) ≤ Real.exp (v * n) := by
    calc
      _ ≤ 8 * ((n : ℝ) + 2) ^ 1 * Real.exp (h δ * n) := by
        simp only [pow_one]
        gcongr
        linarith
      _ ≤ _ := hn₁
  have hlarge : 60 * ((n : ℝ) + 2) ^ 5 * C ^ 5 *
      Real.exp (s * ((1 - δ / 10) * n + 1)) ≤ Real.exp (v * n) := by
    calc
      _ = (60 * C ^ 5 * Real.exp s) * ((n : ℝ) + 2) ^ 5 *
          Real.exp (((1 - δ / 10) * s) * n) := by
        rw [show s * ((1 - δ / 10) * (n : ℝ) + 1) =
          s + ((1 - δ / 10) * s) * n by ring, Real.exp_add]
        ring
      _ ≤ _ := hn₂
  calc
    γ n ≤ _ := hrec δ hδ hδhalf s hs C hC henvC n
    _ ≤ Real.exp (v * n) + Real.exp (v * n) := add_le_add hsmall hlarge
    _ = 2 * (n : ℝ) ^ 0 * Real.exp (v * n) := by ring
    _ ≤ Real.exp (t * n) := hn₃

/-- An entropy term arbitrarily close to zero and a strict section contraction
force subexponential growth. No growth-rate limit is assumed. -/
theorem subexponential_of_envelope_recurrence {γ : ℕ → ℝ} {h : ℝ → ℝ}
    (hinit : ∃ s : ℝ, 0 < s ∧ HasExponentialEnvelope γ s)
    (hsmall : ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 2 ∧ h δ < η)
    (hrec : EnvelopeRecurrence γ h) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, γ n ≤ Real.exp (ε * n) := by
  let rates : Set ℝ := {s | 0 < s ∧ HasExponentialEnvelope γ s}
  have hne : rates.Nonempty := hinit
  have hbd : BddBelow rates := ⟨0, fun s hs => hs.1.le⟩
  have hnonneg : 0 ≤ sInf rates := le_csInf hne (fun s hs => hs.1.le)
  have hzero : sInf rates = 0 := by
    apply le_antisymm _ hnonneg
    by_contra! hpos
    obtain ⟨δ, hδ, hδhalf, hδrate⟩ := hsmall (sInf rates) hpos
    have hqpos : 0 < 1 - δ / 10 := by linarith
    have hqlt : 1 - δ / 10 < 1 := by linarith
    have hinflt : sInf rates < sInf rates / (1 - δ / 10) := by
      apply (lt_div_iff₀ hqpos).2
      nlinarith
    obtain ⟨s, hs, hslt⟩ := exists_lt_of_csInf_lt hne hinflt
    have hqs : (1 - δ / 10) * s < sInf rates := by
      have := (lt_div_iff₀ hqpos).1 hslt
      nlinarith
    obtain ⟨t, htlow, htinf⟩ := exists_between
      (max_lt hpos (max_lt hδrate hqs))
    have htpos : 0 < t := lt_of_le_of_lt (le_max_left _ _) htlow
    have hht : h δ < t := lt_of_le_of_lt
      ((le_max_left _ _).trans (le_max_right _ _)) htlow
    have hqt : (1 - δ / 10) * s < t := lt_of_le_of_lt
      ((le_max_right _ _).trans (le_max_right _ _)) htlow
    have htmem : t ∈ rates := ⟨htpos,
      envelope_recurrence_improves hrec hδ hδhalf hs.1 hs.2 hht hqt⟩
    exact (not_lt_of_ge (csInf_le hbd htmem)) htinf
  intro ε hε
  obtain ⟨s, hs, hsε⟩ := exists_lt_of_csInf_lt hne (by simpa [hzero] using hε)
  exact hs.2.eventually_le hsε

/-- Eventual exponential bounds at every positive rate give the usual normalized
logarithmic growth limit for a sequence bounded below by one. -/
theorem tendsto_log_div_zero_of_subexponential {γ : ℕ → ℝ}
    (hγ : ∀ n : ℕ, 1 ≤ γ n)
    (hsub : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, γ n ≤ Real.exp (ε * n)) :
    Tendsto (fun n : ℕ => Real.log (γ n) / n) atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Filter.Eventually.of_forall fun n =>
      lt_of_lt_of_le ha (div_nonneg (Real.log_nonneg (hγ n)) (Nat.cast_nonneg n))
  · intro ε hε
    filter_upwards [hsub (ε / 2) (by linarith), eventually_ge_atTop 1] with n hn hn1
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (zero_lt_one.trans_le hn1)
    have hlog : Real.log (γ n) ≤ ε / 2 * n :=
      (Real.log_le_iff_le_exp (lt_of_lt_of_le zero_lt_one (hγ n))).2 hn
    have hdiv : Real.log (γ n) / n ≤ ε / 2 := (div_le_iff₀ hnpos).2 hlog
    linarith

/-- Binary entropy can be made arbitrarily small at a strictly positive parameter
less than one half. -/
theorem exists_small_binary_entropy (η : ℝ) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 2 ∧ Real.binEntropy δ < η := by
  obtain ⟨ρ, hρ, hclose⟩ := Metric.continuousAt_iff.1
    (Real.binEntropy_continuous.continuousAt (x := 0)) η hη
  let δ : ℝ := min (ρ / 2) (1 / 4)
  have hδ : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδρ : δ < ρ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hδhalf : δ < 1 / 2 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hd : dist δ 0 < ρ := by simpa [Real.dist_eq, abs_of_pos hδ] using hδρ
  have he := hclose hd
  simp only [Real.binEntropy_zero, Real.dist_eq, sub_zero] at he
  exact ⟨δ, hδ, hδhalf, (le_abs_self _).trans_lt he⟩

/-- The complete numerical consequence needed by the group construction. -/
theorem tendsto_log_div_zero_of_binary_entropy_recurrence {γ : ℕ → ℝ}
    (hγ : ∀ n : ℕ, 1 ≤ γ n)
    (hinit : ∃ s : ℝ, 0 < s ∧ HasExponentialEnvelope γ s)
    (hrec : EnvelopeRecurrence γ Real.binEntropy) :
    Tendsto (fun n : ℕ => Real.log (γ n) / n) atTop (𝓝 0) :=
  tendsto_log_div_zero_of_subexponential hγ
    (subexponential_of_envelope_recurrence hinit exists_small_binary_entropy hrec)

end Kourovka.P21_44
