import Kourovka.Problems.P21_38.Proof.EndpointSlopes
import Mathlib.Data.Nat.Find

/-!
# A first moving affine piece

A nonidentity element of the concrete rational dyadic interval group has a
nontrivial affine piece starting at a fixed dyadic point. The argument uses
only its uniform grid affinity, and does not assume a tree-pair representation.
-/

namespace Kourovka.P21_38

open GroupApproximation.HigmanThompson

/-- An affine map fixing both endpoints of a nondegenerate interval fixes
the entire interval. -/
theorem affineOn_eq_of_fixed_endpoints {f : ℚ → ℚ} {a b s : ℚ}
    (hab : a < b) (hf : AffineOn f a b s) (ha : f a = a) (hb : f b = b) :
    ∀ t : ℚ, a ≤ t → t ≤ b → f t = t := by
  have he := hf b hab.le le_rfl
  rw [ha, hb] at he
  have hs : s = 1 := mul_right_cancel₀ (sub_ne_zero.mpr hab.ne')
    (show s * (b - a) = 1 * (b - a) by linarith)
  intro t hat htb
  have ht := hf t hat htb
  rw [ha, hs] at ht
  linarith

/-- A nonidentity map cannot fix every nonnegative point of a grid on
whose consecutive intervals it is affine. -/
theorem exists_moved_gridPt (g : F) (hg : g ≠ 1) {N B : ℕ}
    (hA : GridAffine 2 (powSlopes 0) g.1 N B) :
    ∃ k : ℕ, g.1 (gridPt 2 N k) ≠ gridPt 2 N k := by
  classical
  by_contra hnone
  have hfix : ∀ k : ℕ, g.1 (gridPt 2 N k) = gridPt 2 N k := by
    simpa only [not_exists, not_not] using hnone
  apply hg
  apply Subtype.ext
  apply Equiv.ext
  intro t
  change g.1 t = t
  by_cases ht : t ≤ 0
  · exact compactF_fix_nonpos g.property ht
  have ht0 : 0 ≤ t := (lt_of_not_ge ht).le
  have hp : (0 : ℚ) < 2 ^ N := by positivity
  let k : ℤ := ⌊t * (2 : ℚ) ^ N⌋
  have hk : 0 ≤ k := Int.floor_nonneg.mpr (mul_nonneg ht0 hp.le)
  have hleft : g.1 (gridPt 2 N k) = gridPt 2 N k := by
    simpa only [Int.toNat_of_nonneg hk] using hfix k.toNat
  have hright : g.1 (gridPt 2 N (k + 1)) = gridPt 2 N (k + 1) := by
    simpa only [Int.toNat_of_nonneg (show 0 ≤ k + 1 by omega)] using hfix (k + 1).toNat
  obtain ⟨s, _, _, haff⟩ := hA.slope k
  have hstep : gridPt 2 N k < gridPt 2 N (k + 1) := by
    simp only [gridPt]
    exact (div_lt_div_iff_of_pos_right hp).mpr (by push_cast; linarith)
  have hbr := floor_bracket (m := 2) N t
  exact affineOn_eq_of_fixed_endpoints hstep haff hleft hright t hbr.1 hbr.2.le

/-- Every nonidentity element has a nontrivial affine germ to the right of
a fixed dyadic point. Its entire displayed interval lies in `[0,1]`. -/
theorem exists_firstMovingPiece (g : F) (hg : g ≠ 1) :
    ∃ α : ℚ, 0 ≤ α ∧ α < 1 ∧ (∃ N : ℕ, α ∈ Grid 2 N) ∧
      ∃ i : ℤ, i ≠ 0 ∧ ∃ δ : ℚ, 0 < δ ∧ α + δ ≤ 1 ∧
        ∀ t : ℚ, α ≤ t → t ≤ α + δ →
          g.1 t = α + (2 : ℚ) ^ i * (t - α) := by
  classical
  obtain ⟨⟨_, ⟨N, B, hA⟩, _⟩, _, _⟩ := g.property
  have hA' : GridAffine 2 (powSlopes 0) g.1 N B := hA
  have hex := exists_moved_gridPt g hg hA'
  let n : ℕ := Nat.find hex
  have hn : g.1 (gridPt 2 N n) ≠ gridPt 2 N n := Nat.find_spec hex
  have hnpos : 0 < n := by
    by_contra h
    have hn0 : n = 0 := by omega
    apply hn
    simpa only [hn0, Nat.cast_zero, gridPt, Int.cast_zero, zero_div] using
      compactF_fix_nonpos g.property (show (0 : ℚ) ≤ 0 by rfl)
  have hprev : g.1 (gridPt 2 N (n - 1 : ℕ)) = gridPt 2 N (n - 1 : ℕ) := by
    exact not_not.mp (Nat.find_min hex (show n - 1 < n by omega))
  have hp : (0 : ℚ) < 2 ^ N := by positivity
  let α : ℚ := gridPt 2 N (n - 1 : ℕ)
  let δ : ℚ := ((2 : ℚ) ^ N)⁻¹
  have hδ : 0 < δ := inv_pos.mpr hp
  have hα : 0 ≤ α := by
    dsimp [α, gridPt]
    exact div_nonneg (by positivity) hp.le
  have hnext : gridPt 2 N n = α + δ := by
    have hncast : (n : ℚ) = ((n - 1 : ℕ) : ℚ) + 1 := by
      exact_mod_cast (show n = (n - 1) + 1 by omega)
    dsimp [α, δ, gridPt]
    push_cast
    rw [hncast]
    ring
  have hbound : α + δ < 1 := by
    by_contra h
    apply hn
    exact compactF_fix_one g.property (by rw [hnext]; exact le_of_not_gt h)
  obtain ⟨s, ⟨i, hi⟩, _, haff⟩ := hA'.slope (n - 1 : ℕ)
  have hs : s = (2 : ℚ) ^ i := by simpa using hi
  have hupper : gridPt 2 N ((n - 1 : ℕ) + 1) = α + δ := by
    have he : (((n - 1 : ℕ) : ℤ) + 1) = (n : ℤ) := by omega
    rw [he, hnext]
  have hformula : ∀ t : ℚ, α ≤ t → t ≤ α + δ →
      g.1 t = α + (2 : ℚ) ^ i * (t - α) := by
    intro t ht0 ht1
    have h := haff t ht0 (by rw [hupper]; exact ht1)
    rw [hprev, hs] at h
    exact h
  have hi0 : i ≠ 0 := by
    intro hi0
    apply hn
    rw [hnext]
    simpa only [hi0, zpow_zero, one_mul, add_sub_cancel_left] using
      hformula (α + δ) (by linarith) le_rfl
  exact ⟨α, hα, by linarith, ⟨N, gridPt_mem N (n - 1 : ℕ)⟩,
    i, hi0, δ, hδ, hbound.le, hformula⟩

end Kourovka.P21_38

#audit_axioms Kourovka.P21_38.exists_firstMovingPiece
