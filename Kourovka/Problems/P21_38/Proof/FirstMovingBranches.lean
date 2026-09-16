import Kourovka.Problems.P21_38.Proof.FirstMovingPiece
import Kourovka.Problems.P21_38.Proof.BinaryDyadic
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# Successive branches of a nonidentity Thompson element

The first moving affine piece yields expanding dynamics for the element or its
inverse. Small binary intervals in that piece give three successive branches,
strictly separated inside the unit interval.
-/

namespace Kourovka.P21_38

open GroupApproximation.HigmanThompson

/-- After replacing an element by its inverse if necessary, its first
moving affine piece has positive exponent. -/
theorem exists_expandingPiece (g : F) (hg : g ≠ 1) :
    ∃ f : F, (f = g ∨ f = g⁻¹) ∧
      ∃ α : ℚ, 0 ≤ α ∧ α < 1 ∧ (∃ N : ℕ, α ∈ Grid 2 N) ∧
        ∃ i : ℤ, 0 < i ∧ ∃ δ : ℚ, 0 < δ ∧ α + δ ≤ 1 ∧
          ∀ t : ℚ, α ≤ t → t ≤ α + δ →
            f.1 t = α + (2 : ℚ) ^ i * (t - α) := by
  obtain ⟨α, hα0, hα1, hgrid, i, hi0, δ, hδ, hbound, hformula⟩ :=
    exists_firstMovingPiece g hg
  rcases lt_or_gt_of_ne hi0 with hi | hi
  · have hp : (0 : ℚ) < 2 ^ i := zpow_pos (by norm_num) i
    have hpinv : (0 : ℚ) < 2 ^ (-i) := zpow_pos (by norm_num) (-i)
    let η : ℚ := min δ ((2 : ℚ) ^ i * δ)
    have hη : 0 < η := lt_min hδ (mul_pos hp hδ)
    refine ⟨g⁻¹, Or.inr rfl, α, hα0, hα1, hgrid,
      -i, neg_pos.mpr hi, η, hη, ?_, ?_⟩
    · have hηδ : η ≤ δ := min_le_left _ _
      linarith
    · intro t ht0 ht1
      let q : ℚ := α + (2 : ℚ) ^ (-i) * (t - α)
      have hq0 : α ≤ q := by
        dsimp [q]
        exact le_add_of_nonneg_right (mul_nonneg hpinv.le (sub_nonneg.mpr ht0))
      have hinv : (2 : ℚ) ^ i * 2 ^ (-i) = 1 := by
        rw [zpow_neg]
        exact mul_inv_cancel₀ hp.ne'
      have hscale : (2 : ℚ) ^ i * (q - α) = t - α := by
        dsimp [q]
        calc
          (2 : ℚ) ^ i * (α + 2 ^ (-i) * (t - α) - α)
              = ((2 : ℚ) ^ i * 2 ^ (-i)) * (t - α) := by ring
          _ = t - α := by rw [hinv, one_mul]
      have htδ : t - α ≤ (2 : ℚ) ^ i * δ := by
        have hηδ : η ≤ (2 : ℚ) ^ i * δ := min_le_right _ _
        linarith
      have hq1 : q ≤ α + δ := by nlinarith
      have hgq : g.1 q = t := by
        rw [hformula q hq0 hq1, hscale]
        ring
      exact Equiv.Perm.inv_eq_iff_eq.mpr hgq.symm
  · exact ⟨g, Or.inl rfl, α, hα0, hα1, hgrid, i, hi,
      δ, hδ, hbound, hformula⟩

namespace BinaryWord

/-- Sufficiently long zero tails put the entire small interval inside any
prescribed right neighborhood of its base point. -/
theorem rightTail_bounds (s : List Bool) {N n : ℕ} (hn : N ≤ n)
    {δ : ℚ} (hsmall : (3 : ℚ) / 2 ^ N < δ) {t : ℚ}
    (ht : t ∈ Set.Icc (0 : ℚ) 1) :
    chart s 0 < chart (rightTail s n) t ∧
      chart (rightTail s n) t < chart s 0 + δ := by
  have hp : (0 : ℚ) < 2 ^ N := by positivity
  have hd : (0 : ℚ) < 2 ^ (s.length + n + 2) := by positivity
  have hden : (2 : ℚ) ^ N ≤ 2 ^ (s.length + n + 2) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hpos : (0 : ℚ) < (2 + t) / 2 ^ (s.length + n + 2) :=
    div_pos (by linarith [ht.1]) hd
  have hnum : (2 + t) / (2 : ℚ) ^ (s.length + n + 2) ≤
      3 / 2 ^ (s.length + n + 2) :=
    (div_le_div_iff_of_pos_right hd).mpr (by linarith [ht.2])
  have hdiv : (3 : ℚ) / 2 ^ (s.length + n + 2) ≤ 3 / 2 ^ N :=
    div_le_div_of_nonneg_left (by norm_num) hp hden
  rw [chart_rightTail]
  constructor <;> linarith

/-- Deleting `e` zeros multiplies displacement from the base point by `2^e`. -/
theorem rightTail_dilate (s : List Bool) (n e : ℕ) (t : ℚ) :
    (2 : ℚ) ^ e * (chart (rightTail s (n + e)) t - chart s 0) =
      chart (rightTail s n) t - chart s 0 := by
  have hpow : (2 : ℚ) ^ (s.length + (n + e) + 2) =
      2 ^ (s.length + n + 2) * 2 ^ e := by
    rw [← pow_add]
    congr 1
    omega
  simp only [chart_rightTail, add_sub_cancel_left, hpow]
  field_simp

/-- Consecutive positive dilates of these intervals have a strict gap. -/
theorem rightTail_separated (s : List Bool) (n e : ℕ) (he : 0 < e) :
    chart (rightTail s (n + e)) 1 < chart (rightTail s n) 0 := by
  have hp : (0 : ℚ) < 2 ^ (s.length + n + 2) := by positivity
  have hpe : (0 : ℚ) < 2 ^ (s.length + (n + e) + 2) := by positivity
  have hpow : (2 : ℚ) ^ (s.length + (n + e) + 2) =
      2 ^ (s.length + n + 2) * 2 ^ e := by
    rw [← pow_add]
    congr 1
    omega
  have he2 : (2 : ℚ) ≤ 2 ^ e := by
    simpa using pow_le_pow_right₀ (show (1 : ℚ) ≤ 2 by norm_num)
      (show 1 ≤ e by omega)
  have hfrac : (3 : ℚ) / 2 ^ (s.length + (n + e) + 2) <
      2 / 2 ^ (s.length + n + 2) := by
    apply (div_lt_div_iff₀ hpe hp).mpr
    rw [hpow]
    nlinarith
  simp only [chart_rightTail, add_zero, show (2 : ℚ) + 1 = 3 by norm_num]
  linarith

end BinaryWord

/-- Every nonidentity element, or its inverse, has two successive branches
between three mixed binary intervals strictly separated inside `(0,1)`. -/
theorem exists_three_successive_branches (g : F) (hg : g ≠ 1) :
    ∃ f : F, (f = g ∨ f = g⁻¹) ∧ ∃ u v w : List Bool,
      HasBranch f.1 u v ∧ HasBranch f.1 v w ∧
      0 < BinaryWord.chart u 0 ∧
      BinaryWord.chart u 1 < BinaryWord.chart v 0 ∧
      BinaryWord.chart v 1 < BinaryWord.chart w 0 ∧
      BinaryWord.chart w 1 < 1 ∧
      (false ∈ u ∧ true ∈ u) ∧ (false ∈ v ∧ true ∈ v) ∧
      (false ∈ w ∧ true ∈ w) := by
  obtain ⟨f, hfg, α, hα0, hα1, ⟨K, hgrid⟩, i, hi, δ, hδ, hbound, hformula⟩ :=
    exists_expandingPiece g hg
  obtain ⟨s, _, hs⟩ := BinaryWord.exists_chart_zero_of_grid hα0 hα1 hgrid
  let e : ℕ := i.toNat
  have he : 0 < e := by dsimp [e]; omega
  have hie : (e : ℤ) = i := Int.toNat_of_nonneg hi.le
  have hpow : (2 : ℚ) ^ i = 2 ^ e := by rw [← hie]; simp
  rw [hpow] at hformula
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt ((3 : ℚ) / δ)
    (show (1 : ℚ) < 2 by norm_num)
  have hpN : (0 : ℚ) < 2 ^ N := by positivity
  have hsmall : (3 : ℚ) / 2 ^ N < δ := by
    apply (div_lt_iff₀ hpN).mpr
    have h := (div_lt_iff₀ hδ).mp hN
    nlinarith
  have hbranch (n : ℕ) (hn : N ≤ n) :
      HasBranch f.1 (BinaryWord.rightTail s (n + e)) (BinaryWord.rightTail s n) := by
    intro t ht
    have hb := BinaryWord.rightTail_bounds s (N := N) (n := n + e)
      (by omega) hsmall ht
    rw [hs] at hb
    rw [hformula _ hb.1.le hb.2.le]
    have hd := BinaryWord.rightTail_dilate s n e t
    rw [hs] at hd
    linarith
  let u := BinaryWord.rightTail s ((N + e) + e)
  let v := BinaryWord.rightTail s (N + e)
  let w := BinaryWord.rightTail s N
  refine ⟨f, hfg, u, v, w, hbranch (N + e) (by omega), hbranch N le_rfl,
    ?_, BinaryWord.rightTail_separated s (N + e) e he,
    BinaryWord.rightTail_separated s N e he, ?_,
    BinaryWord.rightTail_mixed s ((N + e) + e),
    BinaryWord.rightTail_mixed s (N + e), BinaryWord.rightTail_mixed s N⟩
  · have hb := BinaryWord.rightTail_bounds s (N := N) (n := (N + e) + e)
      (by omega) hsmall (show (0 : ℚ) ∈ Set.Icc (0 : ℚ) 1 by constructor <;> norm_num)
    rw [hs] at hb
    exact lt_of_le_of_lt hα0 hb.1
  · have hb := BinaryWord.rightTail_bounds s (N := N) (n := N) le_rfl
      hsmall (show (1 : ℚ) ∈ Set.Icc (0 : ℚ) 1 by constructor <;> norm_num)
    rw [hs] at hb
    exact hb.2.trans_le hbound

end Kourovka.P21_38

#audit_axioms Kourovka.P21_38.exists_expandingPiece
#audit_axioms Kourovka.P21_38.exists_three_successive_branches
