import Kourovka.Problems.P21_38.Proof.FirstMovingPiece
import Mathlib.Data.Finset.Max

/-!
# The last moving affine piece

The rightmost moved vertex of a uniform dyadic grid determines the rightmost
nontrivial affine piece. Beyond its right endpoint the map is the identity.
-/

namespace Kourovka.P21_38

open GroupApproximation.HigmanThompson

/-- A nonidentity element has a last nontrivial affine piece, followed by
pointwise identity. -/
theorem exists_lastMovingPiece (g : F) (hg : g ≠ 1) :
    ∃ β : ℚ, 0 < β ∧ β ≤ 1 ∧ (∃ N : ℕ, β ∈ Grid 2 N) ∧
      (∀ t : ℚ, β ≤ t → g.1 t = t) ∧
      ∃ i : ℤ, i ≠ 0 ∧ ∃ δ : ℚ, 0 < δ ∧ 0 ≤ β - δ ∧
        ∀ t : ℚ, β - δ ≤ t → t ≤ β →
          g.1 t = β + (2 : ℚ) ^ i * (t - β) := by
  classical
  obtain ⟨⟨_, ⟨N, B, hA⟩, _⟩, _, _⟩ := g.property
  have hA' : GridAffine 2 (powSlopes 0) g.1 N B := hA
  have hp : (0 : ℚ) < 2 ^ N := by positivity
  have hmovedBound (k : ℕ) (hk : g.1 (gridPt 2 N k) ≠ gridPt 2 N k) :
      k < 2 ^ N := by
    by_contra hn
    apply hk
    apply compactF_fix_one g.property
    apply (le_div_iff₀ hp).mpr
    have h : (2 : ℚ) ^ N ≤ (k : ℚ) := by exact_mod_cast le_of_not_gt hn
    simpa only [one_mul, Int.cast_natCast] using h
  let s : Finset ℕ := (Finset.range (2 ^ N + 1)).filter
    (fun k => g.1 (gridPt 2 N k) ≠ gridPt 2 N k)
  have hs : s.Nonempty := by
    obtain ⟨k, hk⟩ := exists_moved_gridPt g hg hA'
    exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by
      have := hmovedBound k hk
      omega), hk⟩⟩
  let k : ℕ := s.max' hs
  have hk : g.1 (gridPt 2 N k) ≠ gridPt 2 N k :=
    (Finset.mem_filter.mp (s.max'_mem hs)).2
  have hkbound : k < 2 ^ N := hmovedBound k hk
  have hgridfix (j : ℤ) (hj : (k : ℤ) + 1 ≤ j) :
      g.1 (gridPt 2 N j) = gridPt 2 N j := by
    by_contra hmove
    have hj0 : 0 ≤ j := by omega
    have hmove' : g.1 (gridPt 2 N j.toNat) ≠ gridPt 2 N j.toNat := by
      simpa only [Int.toNat_of_nonneg hj0] using hmove
    have hjmem : j.toNat ∈ s := Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (by have := hmovedBound j.toNat hmove'; omega), hmove'⟩
    have hjk : j.toNat ≤ k := s.le_max' j.toNat hjmem
    omega
  let β : ℚ := gridPt 2 N ((k : ℤ) + 1)
  let δ : ℚ := ((2 : ℚ) ^ N)⁻¹
  have hδ : 0 < δ := inv_pos.mpr hp
  have hβδ : β - δ = gridPt 2 N k := by dsimp [β, δ, gridPt]; push_cast; ring
  have hβ0 : 0 < β := by dsimp [β, gridPt]; positivity
  have hβ1 : β ≤ 1 := by
    dsimp [β, gridPt]
    apply (div_le_iff₀ hp).mpr
    have : (k : ℚ) + 1 ≤ (2 : ℚ) ^ N := by exact_mod_cast hkbound
    simpa using this
  have hfix : ∀ t : ℚ, β ≤ t → g.1 t = t := by
    intro t ht
    let j : ℤ := ⌊t * (2 : ℚ) ^ N⌋
    have hj : (k : ℤ) + 1 ≤ j := by
      apply Int.le_floor.mpr
      have h := (div_le_iff₀ hp).mp ht
      simpa only [β, gridPt, Int.cast_add, Int.cast_natCast, Int.cast_one] using h
    obtain ⟨r, _, _, haff⟩ := hA'.slope j
    have hstep : gridPt 2 N j < gridPt 2 N (j + 1) := by
      simp only [gridPt]
      exact (div_lt_div_iff_of_pos_right hp).mpr (by push_cast; linarith)
    have hbr := floor_bracket (m := 2) N t
    exact affineOn_eq_of_fixed_endpoints hstep haff
      (hgridfix j hj) (hgridfix (j + 1) (by omega)) t hbr.1 hbr.2.le
  obtain ⟨r, ⟨i, hi⟩, _, haff⟩ := hA'.slope k
  have hr : r = (2 : ℚ) ^ i := by simpa using hi
  have hleft : gridPt 2 N k ≤ β := by rw [← hβδ]; linarith
  have he := haff β hleft le_rfl
  rw [hfix β le_rfl, hr] at he
  have hformula : ∀ t : ℚ, β - δ ≤ t → t ≤ β →
      g.1 t = β + (2 : ℚ) ^ i * (t - β) := by
    intro t ht0 ht1
    have ht := haff t (by rwa [← hβδ]) ht1
    rw [hr] at ht
    nlinarith
  have hi0 : i ≠ 0 := by
    intro hi0
    apply hk
    have ht := hformula (β - δ) le_rfl (by linarith)
    simpa [hi0, hβδ] using ht
  refine ⟨β, hβ0, hβ1, ⟨N, gridPt_mem N ((k : ℤ) + 1)⟩,
    hfix, i, hi0, δ, hδ, ?_, hformula⟩
  rw [hβδ]
  dsimp [gridPt]
  positivity

/-- For an element supported away from the endpoints, the last moving
endpoint is strictly inside the unit interval. -/
theorem exists_core_lastMovingPiece {g : Equiv.Perm ℚ}
    (hgcore : g ∈ compactCore 0) (hg : g ≠ 1) :
    ∃ β : ℚ, 0 < β ∧ β < 1 ∧ (∃ N : ℕ, β ∈ Grid 2 N) ∧
      (∀ t : ℚ, β ≤ t → g t = t) ∧
      ∃ i : ℤ, i ≠ 0 ∧ ∃ δ : ℚ, 0 < δ ∧ 0 ≤ β - δ ∧
        ∀ t : ℚ, β - δ ≤ t → t ≤ β →
          g t = β + (2 : ℚ) ^ i * (t - β) := by
  let gF : F := ⟨g, compactCore_le hgcore⟩
  have hgF : gF ≠ 1 := fun he => hg (congrArg Subtype.val he)
  obtain ⟨β, hβ0, hβ1, hgrid, hfix, i, hi, δ, hδ, hbound, hformula⟩ :=
    exists_lastMovingPiece gF hgF
  have hβlt : β < 1 := by
    by_contra hn
    have hβ : β = 1 := le_antisymm hβ1 (le_of_not_gt hn)
    obtain ⟨_, ε, hε, _, hnear⟩ := hgcore
    let η : ℚ := min δ ε / 2
    have hη : 0 < η := div_pos (lt_min hδ hε) (by norm_num)
    have hηδ : η ≤ δ := by dsimp [η]; linarith [min_le_left δ ε]
    have hηε : η ≤ ε := by dsimp [η]; linarith [min_le_right δ ε]
    have ht := hformula (β - η) (by linarith) (by linarith)
    have htfix := hnear (β - η) (by rw [hβ]; linarith)
    change g (β - η) = _ at ht
    rw [htfix] at ht
    have hpone : (2 : ℚ) ^ i = 1 := by nlinarith
    apply hi
    exact (zpow_right_injective₀ (show (0 : ℚ) < 2 by norm_num)
      (show (2 : ℚ) ≠ 1 by norm_num)) (by simpa using hpone)
  exact ⟨β, hβ0, hβlt, hgrid, hfix, i, hi, δ, hδ, hbound, hformula⟩

/-- Inverting if needed makes the last moving piece contract toward its
right endpoint. Both choices remain in every subgroup containing the input. -/
theorem exists_core_contractingLastPiece {g : Equiv.Perm ℚ}
    (hgcore : g ∈ compactCore 0) (hg : g ≠ 1) :
    ∃ f : Equiv.Perm ℚ, (f = g ∨ f = g⁻¹) ∧ f ∈ compactCore 0 ∧
      ∃ β : ℚ, 0 < β ∧ β < 1 ∧ (∃ N : ℕ, β ∈ Grid 2 N) ∧
        (∀ t : ℚ, β ≤ t → f t = t) ∧
        ∃ i : ℤ, i < 0 ∧ ∃ δ : ℚ, 0 < δ ∧ 0 ≤ β - δ ∧
          ∀ t : ℚ, β - δ ≤ t → t ≤ β →
            f t = β + (2 : ℚ) ^ i * (t - β) := by
  obtain ⟨β, hβ0, hβ1, hgrid, hfix, i, hi, δ, hδ, hbound, hformula⟩ :=
    exists_core_lastMovingPiece hgcore hg
  rcases lt_or_gt_of_ne hi with hi | hi
  · exact ⟨g, Or.inl rfl, hgcore, β, hβ0, hβ1, hgrid, hfix,
      i, hi, δ, hδ, hbound, hformula⟩
  · have hp : (0 : ℚ) < 2 ^ i := zpow_pos (by norm_num) i
    have hpinv : (0 : ℚ) < 2 ^ (-i) := zpow_pos (by norm_num) (-i)
    let η : ℚ := min δ ((2 : ℚ) ^ i * δ)
    have hη : 0 < η := lt_min hδ (mul_pos hp hδ)
    refine ⟨g⁻¹, Or.inr rfl, (compactCore 0).inv_mem hgcore,
      β, hβ0, hβ1, hgrid, ?_, -i, neg_neg_of_pos hi, η, hη, ?_, ?_⟩
    · intro t ht
      exact Equiv.Perm.inv_eq_iff_eq.mpr (hfix t ht).symm
    · have : η ≤ δ := min_le_left _ _
      linarith
    · intro t ht0 ht1
      let q : ℚ := β + (2 : ℚ) ^ (-i) * (t - β)
      have hq1 : q ≤ β := by
        dsimp [q]
        exact add_le_of_nonpos_right (mul_nonpos_of_nonneg_of_nonpos hpinv.le (by linarith))
      have hinv : (2 : ℚ) ^ i * 2 ^ (-i) = 1 := by
        rw [zpow_neg]
        exact mul_inv_cancel₀ hp.ne'
      have hscale : (2 : ℚ) ^ i * (q - β) = t - β := by
        dsimp [q]
        calc
          (2 : ℚ) ^ i * (β + 2 ^ (-i) * (t - β) - β)
              = ((2 : ℚ) ^ i * 2 ^ (-i)) * (t - β) := by ring
          _ = t - β := by rw [hinv, one_mul]
      have htδ : β - t ≤ (2 : ℚ) ^ i * δ := by
        have : η ≤ (2 : ℚ) ^ i * δ := min_le_right _ _
        linarith
      have hq0 : β - δ ≤ q := by nlinarith
      have hgq : g q = t := by rw [hformula q hq0 hq1, hscale]; ring
      exact Equiv.Perm.inv_eq_iff_eq.mpr hgq.symm

end Kourovka.P21_38

#audit_axioms Kourovka.P21_38.exists_lastMovingPiece
#audit_axioms Kourovka.P21_38.exists_core_lastMovingPiece
#audit_axioms Kourovka.P21_38.exists_core_contractingLastPiece
