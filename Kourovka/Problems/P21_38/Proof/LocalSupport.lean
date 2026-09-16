import Kourovka.External.GroupApproximation.GroupTheory.HigmanThompson.CompactCore

/-!
# Local motion in the concrete dyadic interval group

These results use the explicit PL moves of the vendored Thompson-group library.
They concern actual permutations of the rationals and require no generation
hypothesis. The point being moved need not itself be dyadic.
-/

namespace Kourovka.P21_38

open GroupApproximation.HigmanThompson

/-- A compact-core element moves any chosen interior rational point, with support
inside any prescribed surrounding subinterval of `[0,1]`. -/
theorem exists_core_supported_move {u z v : ℚ}
    (hu : 0 ≤ u) (huz : u < z) (hzv : z < v) (hv : v ≤ 1) :
    ∃ h ∈ compactCore 0, h z ≠ z ∧
      (∀ t : ℚ, t ≤ u → h t = t) ∧ (∀ t : ℚ, v ≤ t → h t = t) := by
  obtain ⟨α, huα, hαz, hα⟩ := exists_grid_mem_Ioo (m := 0) huz
  obtain ⟨β, hzβ, hβv, hβ⟩ := exists_grid_mem_Ioo (m := 0) hzv
  obtain ⟨N, _, hN⟩ := exists_level (m := 0) 0
    (show (0 : ℚ) < (z - α) / 2 by linarith)
  let δ : ℚ := ((2 : ℚ) ^ N)⁻¹
  have hδ : 0 < δ := inv_pos.mpr (pow_pos (by norm_num) N)
  have hδle : δ ≤ (z - α) / 2 := by simpa [δ] using hN
  have hres : ResEq 0 z (z - δ) := by
    refine ⟨N, 1, ?_⟩
    simp only [Nat.cast_zero, zero_add, zero_add, Int.cast_one, one_mul]
    dsimp [δ]
    rw [sub_sub_cancel, inv_mul_cancel₀ (pow_ne_zero N (by norm_num))]
  obtain ⟨h, hh, hlow, hhigh, hmove⟩ := exists_move 0 hα hβ hres
    hαz (by linarith) hzβ (by linarith)
  refine ⟨h, move_mem_compactCore hh (by linarith) (by linarith) hlow hhigh,
    ?_, ?_, ?_⟩
  · rw [hmove]
    linarith
  · intro t ht
    exact hlow t (by linarith)
  · intro t ht
    exact hhigh t (by linarith)

/-- The compact core has no global fixed point in the open rational interval. -/
theorem exists_core_move {z : ℚ} (hz0 : 0 < z) (hz1 : z < 1) :
    ∃ h ∈ compactCore 0, h z ≠ z := by
  obtain ⟨h, hh, hz, _, _⟩ := exists_core_supported_move (u := 0) (v := 1)
    le_rfl hz0 hz1 le_rfl
  exact ⟨h, hh, hz⟩

/-- Two actual nonidentity elements of the compact core have covering fixed sets. -/
theorem exists_core_pair_covering_fixed_sets :
    ∃ a b : Equiv.Perm ℚ,
      a ∈ compactCore 0 ∧ b ∈ compactCore 0 ∧ a ≠ 1 ∧ b ≠ 1 ∧
        ∀ z : ℚ, a z = z ∨ b z = z := by
  obtain ⟨a, ha, haMove, _, haHigh⟩ :=
    exists_core_supported_move (u := 1 / 8) (z := 3 / 16) (v := 1 / 4)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨b, hb, hbMove, hbLow, _⟩ :=
    exists_core_supported_move (u := 3 / 4) (z := 13 / 16) (v := 7 / 8)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨a, b, ha, hb, ?_, ?_, ?_⟩
  · intro h
    subst a
    exact haMove rfl
  · intro h
    subst b
    exact hbMove rfl
  · intro z
    rcases le_total (1 / 4 : ℚ) z with hz | hz
    · exact Or.inl (haHigh z hz)
    · exact Or.inr (hbLow z (by linarith))

end Kourovka.P21_38
