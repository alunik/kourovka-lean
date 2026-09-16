import Kourovka.External.GroupApproximation.GroupTheory.HigmanThompson.GridAffine
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.FieldSimp

/-!
# Rational fixed points of grid-affine maps

Opposite signs on a rational affine segment give a rational fixed point by
explicit interpolation. A finite induction extends this fact to grid-affine
maps. Thus equal affine endpoint slopes force an interior rational fixed point,
without any appeal to an intermediate value theorem over the rationals.
-/

namespace Kourovka.P21_38

open GroupApproximation.HigmanThompson

/-- An affine rational segment crossing the diagonal has a rational fixed point. -/
theorem rational_affine_fixedPoint
    {f : ℚ → ℚ} {a b s : ℚ} (haff : AffineOn f a b s)
    (hab : a ≤ b) (ha : f a ≤ a) (hb : b ≤ f b) :
    ∃ z, a ≤ z ∧ z ≤ b ∧ f z = z := by
  by_cases hfa : f a = a
  · exact ⟨a, le_rfl, hab, hfa⟩
  have hfa' : f a < a := lt_of_le_of_ne ha hfa
  have hfb := haff b hab le_rfl
  have hs : 0 < s - 1 := by nlinarith
  let z := a + (a - f a) / (s - 1)
  have hza : a ≤ z := by
    dsimp [z]
    exact le_add_of_nonneg_right (div_nonneg (by linarith) hs.le)
  have hzb : z ≤ b := by
    dsimp [z]
    have hdiv : (a - f a) / (s - 1) ≤ b - a := by
      apply (div_le_iff₀ hs).mpr
      nlinarith
    linarith
  have hmul : (s - 1) * (z - a) = a - f a := by
    dsimp [z]
    field_simp
    ring
  refine ⟨z, hza, hzb, ?_⟩
  have hfz := haff z hza hzb
  nlinarith

/-- The reversed crossing has the same conclusion. -/
theorem rational_affine_fixedPoint_reverse
    {f : ℚ → ℚ} {a b s : ℚ} (haff : AffineOn f a b s)
    (hab : a ≤ b) (ha : a ≤ f a) (hb : f b ≤ b) :
    ∃ z, a ≤ z ∧ z ≤ b ∧ f z = z := by
  let g : ℚ → ℚ := fun x => 2 * x - f x
  have hgaff : AffineOn g a b (2 - s) := by
    intro x hax hxb
    dsimp [g]
    rw [haff x hax hxb]
    ring
  obtain ⟨z, hza, hzb, hzg⟩ := rational_affine_fixedPoint hgaff hab
    (by dsimp [g]; linarith) (by dsimp [g]; linarith)
  exact ⟨z, hza, hzb, by dsimp [g] at hzg; linarith⟩

/-- Finitely many rational affine segments retain the diagonal crossing property. -/
theorem rational_piecewise_affine_fixedPoint
    {f : ℚ → ℚ} {p : ℕ → ℚ} (hp : Monotone p) (n : ℕ)
    (haff : ∀ k < n, ∃ s, AffineOn f (p k) (p (k + 1)) s)
    (ha : f (p 0) ≤ p 0) (hb : p n ≤ f (p n)) :
    ∃ z, p 0 ≤ z ∧ z ≤ p n ∧ f z = z := by
  induction n with
  | zero => exact ⟨p 0, le_rfl, le_rfl, le_antisymm ha hb⟩
  | succ n ih =>
    by_cases hn : p n ≤ f (p n)
    · obtain ⟨z, hza, hzb, hz⟩ := ih (fun k hk => haff k (by omega)) hn
      exact ⟨z, hza, hzb.trans (hp (Nat.le_succ n)), hz⟩
    · obtain ⟨s, hs⟩ := haff n (Nat.lt_succ_self n)
      obtain ⟨z, hza, hzb, hz⟩ := rational_affine_fixedPoint hs
        (hp (Nat.le_succ n)) (le_of_not_ge hn) hb
      exact ⟨z, (hp (Nat.zero_le n)).trans hza, hzb, hz⟩

/-- The finite-segment crossing lemma in the other orientation. -/
theorem rational_piecewise_affine_fixedPoint_reverse
    {f : ℚ → ℚ} {p : ℕ → ℚ} (hp : Monotone p) (n : ℕ)
    (haff : ∀ k < n, ∃ s, AffineOn f (p k) (p (k + 1)) s)
    (ha : p 0 ≤ f (p 0)) (hb : f (p n) ≤ p n) :
    ∃ z, p 0 ≤ z ∧ z ≤ p n ∧ f z = z := by
  let g : ℚ → ℚ := fun x => 2 * x - f x
  have hgaff : ∀ k < n, ∃ s, AffineOn g (p k) (p (k + 1)) s := by
    intro k hk
    obtain ⟨s, hs⟩ := haff k hk
    refine ⟨2 - s, ?_⟩
    intro x hax hxb
    dsimp [g]
    rw [hs x hax hxb]
    ring
  obtain ⟨z, hza, hzb, hzg⟩ := rational_piecewise_affine_fixedPoint hp n hgaff
    (by dsimp [g]; linarith) (by dsimp [g]; linarith)
  exact ⟨z, hza, hzb, by dsimp [g] at hzg; linarith⟩

section Grid

variable {m : ℕ} [hm : Fact (1 < m)] {Ω : Submonoid ℚ}

/-- A diagonal crossing between grid points gives a rational fixed point. -/
theorem rational_grid_affine_fixedPoint
    {f : ℚ → ℚ} {N B L : ℕ} (hf : GridAffine m Ω f N B)
    (hL : N ≤ L) (a : ℤ) (n : ℕ)
    (hsigns :
      (f (gridPt m L a) ≤ gridPt m L a ∧
        gridPt m L (a + n) ≤ f (gridPt m L (a + n))) ∨
      (gridPt m L a ≤ f (gridPt m L a) ∧
        f (gridPt m L (a + n)) ≤ gridPt m L (a + n))) :
    ∃ z, gridPt m L a ≤ z ∧ z ≤ gridPt m L (a + n) ∧ f z = z := by
  let p : ℕ → ℚ := fun k => gridPt m L (a + k)
  have hp : Monotone p := by
    intro i j hij
    dsimp [p, gridPt]
    apply div_le_div_of_nonneg_right _ (mPow_pos L).le
    have hc : (i : ℚ) ≤ j := by exact_mod_cast hij
    push_cast
    linarith
  have haff : ∀ k < n, ∃ s, AffineOn f (p k) (p (k + 1)) s := by
    intro k _
    obtain ⟨s, _, _, hs⟩ := hf.affine_fine hL (a + k)
    exact ⟨s, by simpa [p, Nat.cast_add, add_assoc] using hs⟩
  rcases hsigns with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · simpa [p] using rational_piecewise_affine_fixedPoint hp n haff
      (by simpa [p] using ha) hb
  · simpa [p] using rational_piecewise_affine_fixedPoint_reverse hp n haff
      (by simpa [p] using ha) hb

/-- The grid can be refined until its positive step is smaller than any
prescribed positive rational number. -/
theorem exists_fine_grid_step_lt (N : ℕ) {δ : ℚ} (hδ : 0 < δ) :
    ∃ L, N ≤ L ∧ 1 / (m : ℚ) ^ L < δ := by
  have hm' : (1 : ℚ) < m := by exact_mod_cast hm.out
  obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt δ⁻¹ hm'
  refine ⟨max N K, le_max_left N K, ?_⟩
  have hpow : (m : ℚ) ^ K ≤ (m : ℚ) ^ max N K :=
    pow_le_pow_right₀ hm'.le (le_max_right N K)
  have hlt : δ⁻¹ < (m : ℚ) ^ max N K := hK.trans_le hpow
  apply (div_lt_iff₀ (mPow_pos (max N K))).mpr
  have hmul := mul_lt_mul_of_pos_left hlt hδ
  simpa only [mul_inv_cancel₀ hδ.ne'] using hmul

/-- Equal affine endpoint slopes force an interior rational fixed point for a
grid-affine map. The endpoint formulas are needed only in rational neighborhoods
inside the unit interval. -/
theorem rational_grid_affine_interior_fixedPoint
    {f : ℚ → ℚ} {N B : ℕ} (hf : GridAffine m Ω f N B)
    {δ slope : ℚ} (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (hleft : ∀ t, 0 < t → t < δ → f t = slope * t)
    (hright : ∀ t, 1 - δ < t → t < 1 → f t = 1 + slope * (t - 1)) :
    ∃ z : ℚ, 0 < z ∧ z < 1 ∧ f z = z := by
  obtain ⟨L, hNL, htδ⟩ := exists_fine_grid_step_lt (m := m) N hδ
  let t : ℚ := 1 / (m : ℚ) ^ L
  have htpos : 0 < t := one_div_pos.mpr (mPow_pos L)
  have hthalf : t < 1 / 2 := htδ.trans hδhalf
  have hpgt : (2 : ℚ) < (m : ℚ) ^ L := by
    have hmul := (div_lt_iff₀ (mPow_pos L)).mp hthalf
    linarith
  have hnat : 2 ≤ m ^ L := by exact_mod_cast hpgt.le
  have hstart : gridPt m L 1 = t := by simp [gridPt, t]
  have hend : gridPt m L (1 + (m ^ L - 2 : ℕ)) = 1 - t := by
    dsimp [gridPt, t]
    rw [Int.cast_add, Int.cast_one, Int.cast_natCast, Nat.cast_sub hnat]
    push_cast
    field_simp
    ring
  have hft : f t = slope * t := hleft t htpos htδ
  have hfend : f (1 - t) = 1 + slope * ((1 - t) - 1) :=
    hright (1 - t) (by linarith) (by linarith)
  have hsigns :
      (f (gridPt m L 1) ≤ gridPt m L 1 ∧
        gridPt m L (1 + (m ^ L - 2 : ℕ)) ≤
          f (gridPt m L (1 + (m ^ L - 2 : ℕ)))) ∨
      (gridPt m L 1 ≤ f (gridPt m L 1) ∧
        f (gridPt m L (1 + (m ^ L - 2 : ℕ))) ≤
          gridPt m L (1 + (m ^ L - 2 : ℕ))) := by
    rw [hstart, hend, hft, hfend]
    rcases le_total slope 1 with hs | hs
    · exact Or.inl ⟨by nlinarith, by nlinarith⟩
    · exact Or.inr ⟨by nlinarith, by nlinarith⟩
  obtain ⟨z, hza, hzb, hz⟩ := rational_grid_affine_fixedPoint hf hNL
    1 (m ^ L - 2) hsigns
  rw [hstart] at hza
  rw [hend] at hzb
  exact ⟨z, htpos.trans_le hza, by linarith, hz⟩

end Grid

#audit_axioms rational_grid_affine_interior_fixedPoint

end Kourovka.P21_38
