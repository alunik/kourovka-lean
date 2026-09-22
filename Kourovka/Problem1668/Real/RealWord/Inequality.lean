import RealWord.Definitions
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

set_option autoImplicit false

namespace RealWord

private theorem cubic_pos (p : ℝ) (hp : -2 ≤ p) : 0 < p ^ 3 - 4 * p + 4 := by
  rcases le_total p 0 with hp0 | hp0
  · have h : 0 ≤ p * (p - 2) * (p + 2) :=
      mul_nonneg (mul_nonneg_of_nonpos_of_nonpos hp0 (by linarith)) (by linarith)
    nlinarith
  · rcases le_total 2 p with hp2 | hp2
    · have h : 0 ≤ p * (p - 2) * (p + 2) := by positivity
      nlinarith
    · have heq : p ^ 3 - 4 * p + 4 = (p - 1) ^ 2 * (p + 2) + (2 - p) := by ring
      rw [heq]
      by_cases h : p = 2
      · norm_num [h]
      · have h' : 0 < 2 - p := by
          by_contra hn
          apply h
          linarith
        positivity

theorem tracePoly_ge_two (U p : ℝ) (hU : 0 ≤ U) (hp : p ≤ U - 2) :
    2 ≤ tracePoly U p := by
  have hH : 0 < hpoly U p := by
    by_cases hp2 : p < -2
    · have hp0 : p < 0 := by linarith
      have hpp : 0 < p ^ 2 := sq_pos_of_ne_zero (by linarith)
      have hh : 0 ≤ -(U * p * (p ^ 2 - 2)) := by
        have h1 : U * p ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hU (le_of_lt hp0)
        have h2 : 0 ≤ p ^ 2 - 2 := by nlinarith
        exact neg_nonneg.mpr (mul_nonpos_of_nonpos_of_nonneg h1 h2)
      unfold hpoly
      have hsq : 0 ≤ U ^ 2 * (p - 1) ^ 2 := by positivity
      linarith
    · have hc := cubic_pos p (by linarith)
      have heq : hpoly U p = (p - 1) ^ 2 * (U - p - 2) ^ 2 +
          (p ^ 3 - 4 * p + 4) * (U - p - 2) + 4 := by unfold hpoly; ring
      rw [heq]
      have hh : 0 ≤ U - p - 2 := by linarith
      positivity
  unfold tracePoly
  have hh : 0 ≤ U - p - 2 := by linarith
  have hprod : 0 ≤ U * (p - 2) ^ 2 * (p - 1) ^ 2 * (U - p - 2) ^ 3 * hpoly U p := by
    positivity
  linarith

private theorem gap_pos (t : ℝ) (ht : 0 < t) :
    108 * (t + 4) * t ^ 2 * (t + 1) ^ 2 < (4 * t ^ 2 + 7 * t + 4) ^ 3 := by
  have h : 0 < 64 * t ^ 6 + 228 * t ^ 5 + 132 * t ^ 4 + 43 * t ^ 3 +
      348 * t ^ 2 + 336 * t + 64 := by positivity
  nlinarith only [h]

private theorem quartic_bound (D e : ℝ) (hD : 0 < D) (he : 0 ≤ e) :
    D ^ 3 * (e ^ 3 * (4 - D * e)) ≤ 27 := by
  have h : 0 ≤ (D * e - 3) ^ 2 * ((D * e + 1) ^ 2 + 2) := by positivity
  nlinarith only [h]

theorem tracePoly_gt_seven_fourths (U p : ℝ) (hU : 0 ≤ U)
    (hdom : p ≤ U - 2 ∨ 4 < U) : (7 : ℝ) / 4 < tracePoly U p := by
  by_cases hp : p ≤ U - 2
  · have h := tracePoly_ge_two U p hU hp
    linarith
  · have hU4 : 4 < U := hdom.resolve_left hp
    let t := p - 2
    let e := p - U + 2
    let D := 4 * t ^ 2 + 7 * t + 4
    have ht : 0 < t := by dsimp [t]; linarith
    have he : 0 < e := by dsimp [e]; linarith
    have het : e < t := by dsimp [e, t]; linarith
    have hD : 0 < D := by dsimp [D]; positivity
    have hUeq : U = t + 4 - e := by dsimp [t, e]; ring
    have hpeq : p = t + 2 := by dsimp [t]; ring
    have hH : hpoly U p ≤ 4 - D * e := by
      have h : 0 ≤ e * (t - e) * (t + 1) ^ 2 := by positivity
      rw [hUeq, hpeq]
      dsimp [hpoly, D]
      nlinarith only [h]
    have htr : tracePoly U p = 2 - U * t ^ 2 * (t + 1) ^ 2 * e ^ 3 * hpoly U p := by
      unfold tracePoly
      dsimp [t, e]
      ring
    by_cases hH0 : hpoly U p ≤ 0
    · have hnon : U * t ^ 2 * (t + 1) ^ 2 * e ^ 3 * hpoly U p ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) hH0
      rw [htr]
      linarith
    · have hHpos : 0 < hpoly U p := by linarith
      have h4 : 0 < 4 - D * e := lt_of_lt_of_le hHpos hH
      let L := (t + 4) * t ^ 2 * (t + 1) ^ 2
      let delta := U * t ^ 2 * (t + 1) ^ 2 * e ^ 3 * hpoly U p
      have hL : 0 ≤ L := by dsimp [L]; positivity
      have hdelta : delta ≤ L * (e ^ 3 * (4 - D * e)) := by
        have hfirst : U * t ^ 2 * (t + 1) ^ 2 * e ^ 3 * hpoly U p ≤
            U * t ^ 2 * (t + 1) ^ 2 * e ^ 3 * (4 - D * e) :=
          mul_le_mul_of_nonneg_left hH (by positivity)
        have hsecond : U * (t ^ 2 * (t + 1) ^ 2 * e ^ 3 * (4 - D * e)) ≤
            (t + 4) * (t ^ 2 * (t + 1) ^ 2 * e ^ 3 * (4 - D * e)) :=
          mul_le_mul_of_nonneg_right (by linarith [hUeq]) (by positivity)
        dsimp [delta, L]
        nlinarith only [hfirst, hsecond]
      have hmax := quartic_bound D e hD (le_of_lt he)
      have hmul := mul_le_mul_of_nonneg_left hdelta (le_of_lt (pow_pos hD 3))
      have hmaxL := mul_le_mul_of_nonneg_left hmax hL
      have hdeltaD : D ^ 3 * delta ≤ 27 * L := by
        nlinarith only [hmul, hmaxL]
      have hgap : 108 * L < D ^ 3 := by
        simpa only [L, D, mul_assoc] using gap_pos t ht
      have hdelta_lt : delta < (1 : ℝ) / 4 := by
        have hD3 := pow_pos hD 3
        nlinarith only [hdeltaD, hgap, hD3]
      rw [htr]
      change (7 : ℝ) / 4 < 2 - delta
      linarith

end RealWord
