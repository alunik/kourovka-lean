import Kourovka.Problems.P21_38.Proof.LastMovingPiece
import Kourovka.Problems.P21_38.Proof.LocalInterpolation
import Kourovka.Problems.P21_38.Proof.CompanionTrees

/-!
# Motion by interval fixers

Deep branch communication and a nontrivial compactly supported element give
motion across every real cut to the left of a fixed binary interval.
-/

namespace Kourovka.P21_38

open GroupApproximation.HigmanThompson BinaryWord Set

namespace BinaryWord

/-- A binary interval contains a real cut in a unique half-open descendant
at any prescribed depth. -/
theorem exists_real_descendant (w : List Bool) (n : ℕ) {c : ℝ}
    (hc0 : (chart w 0 : ℝ) ≤ c) (hc1 : c < (chart w 1 : ℝ)) :
    ∃ s : List Bool, s.length = n ∧
      (chart (w ++ s) 0 : ℝ) ≤ c ∧ c < (chart (w ++ s) 1 : ℝ) := by
  induction n generalizing w with
  | zero => exact ⟨[], rfl, by simpa using hc0, by simpa using hc1⟩
  | succ n ih =>
    have hleft : chart (w ++ [false]) 0 = chart w 0 := by simp [chart_append, chart]
    have hright : chart (w ++ [true]) 1 = chart w 1 := by simp [chart_append, chart]
    have hmid : chart (w ++ [false]) 1 = chart (w ++ [true]) 0 := by
      norm_num [chart_append, chart]
    by_cases hc : c < (chart (w ++ [false]) 1 : ℝ)
    · obtain ⟨s, hs, hs0, hs1⟩ := ih (w ++ [false]) (by simpa [hleft] using hc0) hc
      exact ⟨false :: s, by simp [hs], by simpa [List.append_assoc] using hs0,
        by simpa [List.append_assoc] using hs1⟩
    · obtain ⟨s, hs, hs0, hs1⟩ := ih (w ++ [true])
        (by rw [← hmid]; exact le_of_not_gt hc) (by simpa [hright] using hc1)
      exact ⟨true :: s, by simp [hs], by simpa [List.append_assoc] using hs0,
        by simpa [List.append_assoc] using hs1⟩

theorem chart_zero_eq_zero_of_not_mem_true {w : List Bool} (h : true ∉ w) :
    chart w 0 = 0 := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    have hb : b = false := by cases b <;> simp_all
    subst b
    simp only [chart_cons, Bool.false_eq_true, ↓reduceIte, zero_add]
    rw [ih (fun hh => h (List.mem_cons_of_mem _ hh))]
    norm_num

theorem chart_one_eq_one_of_not_mem_false {w : List Bool} (h : false ∉ w) :
    chart w 1 = 1 := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    have hb : b = true := by cases b <;> simp_all
    subst b
    simp only [chart_cons, ↓reduceIte]
    rw [ih (fun hh => h (List.mem_cons_of_mem _ hh))]
    norm_num

theorem mixed_of_interior {w : List Bool} (h0 : 0 < chart w 0) (h1 : chart w 1 < 1) :
    false ∈ w ∧ true ∈ w := by
  constructor
  · by_contra h
    rw [chart_one_eq_one_of_not_mem_false h] at h1
    exact lt_irrefl _ h1
  · by_contra h
    rw [chart_zero_eq_zero_of_not_mem_true h] at h0
    exact lt_irrefl _ h0

/-- A sufficiently fine binary interval brackets an interior real cut and
lies strictly below a prescribed rational upper bound. -/
theorem exists_real_bracket {c : ℝ} {α : ℚ}
    (hc0 : 0 < c) (hcα : c < (α : ℝ)) (hα1 : α ≤ 1) :
    ∃ w : List Bool, (false ∈ w ∧ true ∈ w) ∧
      (chart w 0 : ℝ) ≤ c ∧ c < (chart w 1 : ℝ) ∧ chart w 1 < α := by
  let ε : ℝ := min c ((α : ℝ) - c)
  have hε : 0 < ε := lt_min hc0 (sub_pos.mpr hcα)
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (1 / ε) (show (1 : ℝ) < 2 by norm_num)
  have hp : (0 : ℝ) < 2 ^ n := by positivity
  have hsmall : (1 : ℝ) / 2 ^ n < ε := by
    apply (div_lt_iff₀ hp).mpr
    have h := (div_lt_iff₀ hε).mp hn
    nlinarith
  obtain ⟨w, hwlen, hw0, hw1⟩ := exists_real_descendant [] n
    (by simpa using hc0.le) (by
      have : c < (1 : ℝ) := hcα.trans_le (by exact_mod_cast hα1)
      simpa using this)
  simp only [List.nil_append] at hw0 hw1
  have hwidth : (chart w 1 : ℝ) = (chart w 0 : ℝ) + 1 / 2 ^ n := by
    have h := chart_affine w 1
    rw [hwlen] at h
    simpa using congrArg (fun q : ℚ => (q : ℝ)) h
  have hleft : 0 < chart w 0 := by
    have hec : ε ≤ c := min_le_left _ _
    have : (0 : ℝ) < (chart w 0 : ℝ) := by linarith
    exact_mod_cast this
  have hright : chart w 1 < α := by
    have heα : ε ≤ (α : ℝ) - c := min_le_right _ _
    have : (chart w 1 : ℝ) < (α : ℝ) := by linarith
    exact_mod_cast this
  exact ⟨w, mixed_of_interior hleft (hright.trans_le hα1), hw0, hw1, hright⟩

theorem chart_complement (w : List Bool) (t : ℚ) :
    chart (w.map Bool.not) t = 1 - chart w (1 - t) := by
  induction w with
  | nil => simp
  | cons b w ih => cases b <;> simp [chart, ih] <;> ring

theorem chart_replicate_true (n : ℕ) (t : ℚ) :
    chart (List.replicate n true) t = 1 - (1 - t) / 2 ^ n := by
  have h := chart_complement (List.replicate n false) t
  simpa [chart_replicate_false] using h

/-- Every interior dyadic point is the right endpoint of a mixed binary
interval lying in any prescribed left neighborhood. -/
theorem exists_mixed_left_neighborhood {β δ : ℚ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hgrid : ∃ N : ℕ, β ∈ Grid 2 N)
    (hδ : 0 < δ) :
    ∃ w : List Bool, (false ∈ w ∧ true ∈ w) ∧
      chart w 1 = β ∧ β - δ ≤ chart w 0 := by
  obtain ⟨K, hK⟩ := hgrid
  obtain ⟨s, _, hs⟩ := exists_chart_zero_of_grid (by linarith : 0 ≤ 1 - β)
    (by linarith : 1 - β < 1) (grid_sub (int_mem_grid (m := 2) K 1) hK)
  let v := s.map Bool.not
  have hv : chart v 1 = β := by simp [v, chart_complement, hs]
  let ε : ℚ := min δ β
  have hε : 0 < ε := lt_min hδ hβ0
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (1 / ε) (show (1 : ℚ) < 2 by norm_num)
  have hp : (0 : ℚ) < 2 ^ n := by positivity
  have hsmall : (1 : ℚ) / 2 ^ n < ε := by
    apply (div_lt_iff₀ hp).mpr
    have h := (div_lt_iff₀ hε).mp hn
    nlinarith
  let w := v ++ List.replicate n true
  have hw1 : chart w 1 = β := by simp [w, chart_append, chart_replicate_true, hv]
  have hden : (2 : ℚ) ^ n ≤ 2 ^ w.length := by
    apply pow_le_pow_right₀ (by norm_num)
    simp [w]
  have hwidth : β - chart w 0 = 1 / (2 : ℚ) ^ w.length := by
    have := chart_affine w 1
    rw [hw1] at this
    linarith
  have hwd : β - chart w 0 < ε := (hwidth.le.trans
    (div_le_div_of_nonneg_left (by norm_num) hp hden)).trans_lt hsmall
  have hw0 : 0 < chart w 0 := by have := min_le_right δ β; linarith
  refine ⟨w, mixed_of_interior hw0 (by simpa [hw1] using hβ1), hw1, ?_⟩
  have := min_le_left δ β
  linarith

end BinaryWord

/-- An affine contraction toward a right endpoint changes every real cut
in the corresponding half-open interval, including its rational left endpoint. -/
theorem affine_contraction_changes_cut
    {H : Subgroup (Equiv.Perm ℚ)} {k : Equiv.Perm ℚ} (hk : k ∈ H)
    (hkmono : StrictMono k) {l r slope : ℚ} (hslope0 : 0 < slope) (hslope1 : slope < 1)
    (hformula : ∀ t : ℚ, l ≤ t → t ≤ r → k t = r + slope * (t - r))
    {c : ℝ} (hlc : (l : ℝ) ≤ c) (hcr : c < (r : ℝ)) :
    ∃ f ∈ H, ∃ q : ℚ, ¬ ((f q : ℝ) < c ↔ (q : ℝ) < c) := by
  have hlr : l < r := by exact_mod_cast hlc.trans_lt hcr
  have hslope0R : (0 : ℝ) < slope := by exact_mod_cast hslope0
  have hslope1R : (slope : ℝ) < 1 := by exact_mod_cast hslope1
  rcases hlc.eq_or_lt with hc | hc
  · have hkl : l < k l := by
      rw [hformula l le_rfl hlr.le]
      have := mul_pos (sub_pos.mpr hslope1) (sub_pos.mpr hlr)
      nlinarith
    have hinv : k⁻¹ l < l := hkmono.lt_iff_lt.mp (by simpa using hkl)
    refine ⟨k⁻¹, H.inv_mem hk, l, ?_⟩
    intro he
    have hleft : (k⁻¹ l : ℝ) < c := by rw [← hc]; exact_mod_cast hinv
    have hright := he.mp hleft
    rw [hc] at hright
    exact lt_irrefl _ hright
  · let T : ℝ := (c - (1 - slope) * r) / slope
    have hTc : T < c := by
      apply (div_lt_iff₀ hslope0R).mpr
      have := mul_pos (sub_pos.mpr hslope1R) (sub_pos.mpr hcr)
      nlinarith
    obtain ⟨q, hqlo, hqc⟩ := exists_rat_btwn (max_lt hc hTc)
    have hlq : l ≤ q := by exact_mod_cast (le_max_left (l : ℝ) T).trans hqlo.le
    have hqr : q ≤ r := by exact_mod_cast (hqc.trans hcr).le
    have hTq : T < (q : ℝ) := (le_max_right _ _).trans_lt hqlo
    have hprod := mul_lt_mul_of_pos_left hTq hslope0R
    have hTeq : (slope : ℝ) * T = c - (1 - slope) * r := by
      dsimp [T]
      exact mul_div_cancel₀ _ hslope0R.ne'
    have hqformula : (k q : ℝ) = r + (slope : ℝ) * (q - r) := by
      exact_mod_cast hformula q hlq hqr
    have hmove : c < (k q : ℝ) := by nlinarith
    exact ⟨k, hk, q, fun he => (not_lt_of_gt hmove) (he.mpr hqc)⟩

/-- Conjugating a contraction through one affine branch transports its
formula to the source interval. -/
theorem conjugate_branch_contraction
    {f h : Equiv.Perm ℚ} (hfmono : StrictMono f) {v w : List Bool}
    (hf : HasBranch f v w) {β δ slope : ℚ}
    (hw1 : chart w 1 = β) (hw0 : β - δ ≤ chart w 0)
    (hslope0 : 0 < slope) (hslope1 : slope < 1)
    (hformula : ∀ t : ℚ, β - δ ≤ t → t ≤ β → h t = β + slope * (t - β)) :
    ∀ t : ℚ, chart v 0 ≤ t → t ≤ chart v 1 →
      (f⁻¹ * h * f) t = chart v 1 + slope * (t - chart v 1) := by
  intro t ht0 ht1
  let q : ℚ := chart v 1 + slope * (t - chart v 1)
  have hq0 : chart v 0 ≤ q := by
    have hgap := mul_nonneg (sub_nonneg.mpr hslope1.le) (sub_nonneg.mpr ht1)
    dsimp [q]
    nlinarith
  have hq1 : q ≤ chart v 1 := by
    dsimp [q]
    exact add_le_of_nonpos_right (mul_nonpos_of_nonneg_of_nonpos hslope0.le (sub_nonpos.mpr ht1))
  have hft0 : β - δ ≤ f t := by
    have h := hfmono.monotone ht0
    rw [hf.left_endpoint] at h
    exact hw0.trans h
  have hft1 : f t ≤ β := by
    have h := hfmono.monotone ht1
    rwa [hf.right_endpoint, hw1] at h
  have he : h (f t) = f q := by
    rw [hformula _ hft0 hft1, hf.affine_formula_right ht0 ht1,
      hf.affine_formula_right hq0 hq1, hw1]
    dsimp [q]
    ring
  change f⁻¹ (h (f t)) = q
  rw [he]
  exact Equiv.symm_apply_apply f q

/-- Deep branch communication and a nontrivial core element ensure that
the pointwise fixer of any binary interval changes every real cut to its left. -/
theorem wordFixer_noInvariantRealCut_of_deep_branches
    {H : Subgroup (Equiv.Perm ℚ)} (hH : H ≤ compactF 0 1)
    (hdeep : DeepBranchCommunication H)
    (hcore : ∃ g ∈ H, g ∈ compactCore 0 ∧ g ≠ 1) (u : List Bool) :
    NoInvariantRealCut (wordFixer H u) 0 (chart u 0) := by
  obtain ⟨g, hg, hgcore, hg1⟩ := hcore
  obtain ⟨h, hhg, _, β, hβ0, hβ1, hgrid, hfix, i, hi, δ, hδ, _, hformula⟩ :=
    exists_core_contractingLastPiece hgcore hg1
  have hh : h ∈ H := by rcases hhg with rfl | rfl; exact hg; exact H.inv_mem hg
  obtain ⟨v, hvmix, hv1, hv0⟩ := exists_mixed_left_neighborhood hβ0 hβ1 hgrid hδ
  intro c hc0 hcα
  have hc0' : 0 < c := by simpa using hc0
  obtain ⟨w, hwmix, hw0, hw1, hwα⟩ := exists_real_bracket hc0' hcα
    (chart_mem_unit u (show (0 : ℚ) ∈ Icc 0 1 by constructor <;> norm_num)).2
  obtain ⟨N, hN⟩ := hdeep w v hwmix hvmix
  obtain ⟨s, hs, hs0, hs1⟩ := exists_real_descendant w N hw0 hw1
  obtain ⟨f, hfH, hf⟩ := hN s (List.replicate N true) hs.ge (by simp)
  have hfmono := compactF_strictMono (hH hfH)
  let a := w ++ s
  let b := v ++ List.replicate N true
  have hb1 : chart b 1 = β := by simp [b, chart_append, chart_replicate_true, hv1]
  have hb0 : β - δ ≤ chart b 0 := by
    apply hv0.trans
    dsimp [b]
    rw [chart_append]
    exact (chart_strictMono v).monotone
      (chart_mem_unit (List.replicate N true) (show (0 : ℚ) ∈ Icc 0 1 by constructor <;> norm_num)).1
  have haα : chart a 1 < chart u 0 := by
    apply lt_of_le_of_lt ?_ hwα
    dsimp [a]
    rw [chart_append]
    exact (chart_strictMono w).monotone
      (chart_mem_unit s (show (1 : ℚ) ∈ Icc 0 1 by constructor <;> norm_num)).2
  let k : Equiv.Perm ℚ := f⁻¹ * h * f
  have hkH : k ∈ H := H.mul_mem (H.mul_mem (H.inv_mem hfH) hh) hfH
  have hkfix : ∀ t : ℚ, chart u 0 ≤ t → k t = t := by
    intro t ht
    have hβft : β ≤ f t := by
      have h := hfmono (haα.trans_le ht)
      rw [hf.right_endpoint, hb1] at h
      exact h.le
    change f⁻¹ (h (f t)) = t
    rw [hfix (f t) hβft]
    exact Equiv.symm_apply_apply f t
  have hk : k ∈ wordFixer H u := ⟨hkH, fun t ht => hkfix _
    ((chart_strictMono u).monotone ht.1)⟩
  have hslope0 : (0 : ℚ) < 2 ^ i := zpow_pos (by norm_num) i
  have hslope1 : (2 : ℚ) ^ i < 1 := zpow_lt_one_of_neg₀ (by norm_num) hi
  exact affine_contraction_changes_cut hk (compactF_strictMono (hH hkH)) hslope0 hslope1
    (conjugate_branch_contraction hfmono hf hb1 hb0 hslope0 hslope1 hformula) hs0 hs1

#audit_axioms BinaryWord.exists_real_bracket
#audit_axioms BinaryWord.exists_mixed_left_neighborhood
#audit_axioms affine_contraction_changes_cut
#audit_axioms conjugate_branch_contraction
#audit_axioms wordFixer_noInvariantRealCut_of_deep_branches

end Kourovka.P21_38
