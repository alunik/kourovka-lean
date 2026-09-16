import Kourovka.Problems.P21_38.Proof.BinaryDyadic
import Kourovka.Problems.P21_38.Proof.BinaryPartitions
import Kourovka.Problems.P21_38.Proof.EndpointSlopes
import Mathlib.Data.List.OfFn

/-!
# Binary branch partitions of actual PL elements

The grid-affine definition of the concrete interval group yields finite paired
binary partitions. This is the converse construction to tree-pair realization;
no tree-pair representation is assumed in the definition of `F`.
-/

namespace Kourovka.P21_38

open GroupApproximation.HigmanThompson BinaryWord

private theorem unit_grid_bounds (L i : ℕ) (hi : i < 2 ^ L) :
    0 ≤ gridPt 2 L i ∧ gridPt 2 L i < gridPt 2 L (i + 1) ∧
      gridPt 2 L (i + 1) ≤ 1 := by
  have hp : (0 : ℚ) < 2 ^ L := by positivity
  have hiq : (i : ℚ) + 1 ≤ (2 : ℚ) ^ L := by exact_mod_cast hi
  simp only [gridPt, Nat.cast_ofNat, Int.cast_natCast, Int.cast_add, Int.cast_one]
  exact ⟨div_nonneg (Nat.cast_nonneg i) hp.le,
    (div_lt_div_iff_of_pos_right hp).mpr (by linarith),
    (div_le_one hp).mpr hiq⟩

/-- On a coarse unit-interval cell a slope cannot exceed the reciprocal of
the cell's width, because the whole image lies in the unit interval. -/
private theorem coarse_slope_bound (f : F) {N : ℕ} {j k : ℤ}
    (hj0 : 0 ≤ j) (hj1 : j + 1 ≤ (2 : ℤ) ^ N)
    (haff : AffineOn f.1 (gridPt 2 N j) (gridPt 2 N (j + 1)) ((2 : ℚ) ^ k)) :
    k ≤ (N : ℤ) := by
  have hp : (0 : ℚ) < 2 ^ N := by positivity
  have ha0 : 0 ≤ gridPt 2 N j := by
    exact div_nonneg (by exact_mod_cast hj0) hp.le
  have hb1 : gridPt 2 N (j + 1) ≤ 1 := by
    apply (div_le_one hp).mpr
    exact_mod_cast hj1
  have hab : gridPt 2 N j ≤ gridPt 2 N (j + 1) := by
    apply (div_le_div_iff_of_pos_right hp).mpr
    push_cast
    linarith
  have hfa : 0 ≤ f.1 (gridPt 2 N j) := by
    simpa only [compactF_fix_nonpos f.property le_rfl] using
      (compactF_strictMono f.property).monotone ha0
  have hfb : f.1 (gridPt 2 N (j + 1)) ≤ 1 := by
    simpa only [compactF_fix_one f.property le_rfl] using
      (compactF_strictMono f.property).monotone hb1
  have heq := haff _ hab le_rfl
  have hwidth : gridPt 2 N (j + 1) - gridPt 2 N j = 1 / (2 : ℚ) ^ N := by
    simp only [gridPt, Nat.cast_ofNat, Int.cast_add, Int.cast_one]
    ring
  rw [hwidth] at heq
  have hs : (2 : ℚ) ^ k ≤ (2 : ℚ) ^ N := by
    have h := mul_le_mul_of_nonneg_right (show (2 : ℚ) ^ k * (1 / (2 : ℚ) ^ N) ≤ 1 by
      linarith) hp.le
    simpa only [mul_assoc, one_div_mul_cancel hp.ne', mul_one, one_mul] using h
  apply (zpow_le_zpow_iff_right₀ (show (1 : ℚ) < 2 by norm_num)).mp
  simpa only [zpow_natCast] using hs

/-- A sufficiently fine domain grid has standard binary images, with an
explicit target level depending on the affine slope of each cell. -/
private theorem fine_cell_branch (f : F) {N B : ℕ}
    (hf : GridAffine 2 (powSlopes 0) f.1 N B)
    (i : ℕ) (hi : i < 2 ^ (N + B)) :
    ∃ u v : List Bool,
      chart u 0 = gridPt 2 (N + B) i ∧
      chart u 1 = gridPt 2 (N + B) (i + 1) ∧ HasBranch f.1 u v := by
  let L := N + B
  have hNL : N ≤ L := Nat.le_add_right N B
  obtain ⟨hx0, hxy, hy1⟩ := unit_grid_bounds L i hi
  obtain ⟨j, hjx, hyj⟩ := exists_bracket_of_no_grid (m := 2) (M := N)
    (u := gridPt 2 L i) (v := gridPt 2 L (i + 1))
    (fun q hq => not_between_consecutive (grid_mono hNL hq))
  have hpN : (0 : ℚ) < 2 ^ N := by positivity
  have hpL : (0 : ℚ) < 2 ^ L := by positivity
  have hj0 : 0 ≤ j := by
    have hb : (0 : ℚ) < gridPt 2 N (j + 1) := lt_of_lt_of_le (lt_of_le_of_lt hx0 hxy) hyj
    have hjq : (0 : ℚ) < (j : ℚ) + 1 := by
      have := (lt_gridPt_iff.mp hb)
      simpa using this
    have : (0 : ℤ) < j + 1 := by exact_mod_cast hjq
    omega
  have hj1 : j + 1 ≤ (2 : ℤ) ^ N := by
    have ha : gridPt 2 N j < 1 := lt_of_le_of_lt hjx (lt_of_lt_of_le hxy hy1)
    have hjq : (j : ℚ) < (2 : ℚ) ^ N := by simpa using gridPt_lt_iff.mp ha
    have : j < (2 : ℤ) ^ N := by exact_mod_cast hjq
    omega
  obtain ⟨s, hs, _, haff⟩ := hf.slope j
  obtain ⟨k, hk⟩ := hs
  have hsk : s = (2 : ℚ) ^ k := by simpa using hk
  rw [hsk] at haff
  have hkN := coarse_slope_bound f hj0 hj1 haff
  let M := ((L : ℤ) - k).toNat
  have hM : (M : ℤ) = (L : ℤ) - k := Int.toNat_of_nonneg (by omega)
  have hBM : B ≤ M := by omega
  have hpow : (2 : ℚ) ^ k * (2 : ℚ) ^ M = (2 : ℚ) ^ L := by
    rw [← zpow_natCast, ← zpow_add₀ (show (2 : ℚ) ≠ 0 by norm_num), hM]
    convert (zpow_natCast (2 : ℚ) L) using 1
    congr 1
    omega
  have hgrid : f.1 (gridPt 2 L i) ∈ Grid 2 M := by
    rw [haff _ hjx (hxy.le.trans hyj)]
    apply grid_add (grid_mono hBM (hf.value j))
    obtain ⟨d, hd⟩ := grid_sub (gridPt_mem (m := 2) L (i : ℤ))
      (grid_mono hNL (gridPt_mem (m := 2) N j))
    refine ⟨d, ?_⟩
    norm_num only [Nat.cast_ofNat] at hd ⊢
    calc (2 : ℚ) ^ k * (gridPt 2 L i - gridPt 2 N j) * 2 ^ M =
        (gridPt 2 L i - gridPt 2 N j) * 2 ^ L := by rw [← hpow]; ring
      _ = d := hd
  have hfx0 : 0 ≤ f.1 (gridPt 2 L i) := by
    simpa only [compactF_fix_nonpos f.property le_rfl] using
      (compactF_strictMono f.property).monotone hx0
  have hfx1 : f.1 (gridPt 2 L i) < 1 := by
    simpa only [compactF_fix_one f.property le_rfl] using
      compactF_strictMono f.property (lt_of_lt_of_le hxy hy1)
  obtain ⟨u, hulen, hu⟩ := exists_chart_zero_eq_nat_div L i hi
  have hu0 : chart u 0 = gridPt 2 L i := by simpa only [gridPt, Nat.cast_ofNat, Int.cast_natCast] using hu
  have hu1 : chart u 1 = gridPt 2 L (i + 1) := by
    rw [chart_affine, hulen, hu]
    simp only [gridPt, Nat.cast_ofNat, Int.cast_add, Int.cast_natCast, Int.cast_one]
    ring
  obtain ⟨v, hvlen, hv⟩ := exists_chart_zero_of_grid hfx0 hfx1 hgrid
  refine ⟨u, v, hu0, hu1, ?_⟩
  intro t ht
  have hut0 : gridPt 2 L i ≤ chart u t := by
    rw [← hu0]
    exact (chart_strictMono u).monotone ht.1
  have hut1 : chart u t ≤ gridPt 2 L (i + 1) := by
    rw [← hu1]
    exact (chart_strictMono u).monotone ht.2
  rw [(haff.restrict hjx hyj) _ hut0 hut1]
  rw [chart_affine u, chart_affine v, hu0, hv, hulen, hvlen]
  have hpM : (2 : ℚ) ^ M ≠ 0 := by positivity
  have hscale : (2 : ℚ) ^ k * (t / 2 ^ L) = t / 2 ^ M := by
    apply (eq_div_iff hpM).mpr
    calc (2 : ℚ) ^ k * (t / 2 ^ L) * 2 ^ M =
        t / 2 ^ L * 2 ^ L := by rw [← hpow]; ring
      _ = t := div_mul_cancel₀ _ hpL.ne'
  simp only [add_sub_cancel_left, hscale]

/-- All sufficiently fine uniform domain grids admit binary image branches. -/
theorem exists_eventual_grid_branches (f : F) :
    ∃ K : ℕ, ∀ L : ℕ, K ≤ L → ∀ i : ℕ, i < 2 ^ L →
      ∃ u v : List Bool, chart u 0 = gridPt 2 L i ∧
        chart u 1 = gridPt 2 L (i + 1) ∧ HasBranch f.1 u v := by
  obtain ⟨N, B, hf⟩ := f.property.1.2.1
  refine ⟨N + B, fun L hL i hi => ?_⟩
  have hN : N ≤ L := by omega
  have hB : B ≤ L - N := by omega
  have heq : N + (L - N) = L := Nat.add_sub_of_le hN
  have h := fine_cell_branch f (hf.mono_bound hB) i (by simpa only [heq] using hi)
  simpa only [heq] using h

/-- Consecutive endpoint formulas assemble an indexed family of words into
an ordered complete partition. -/
theorem WordPartition.ofFn {n : ℕ} (ws : Fin n → List Bool) (p : ℕ → ℚ)
    (hl : ∀ i, chart (ws i) 0 = p i.val)
    (hr : ∀ i, chart (ws i) 1 = p (i.val + 1)) :
    WordPartition (p 0) (p n) (List.ofFn ws) := by
  induction n generalizing p with
  | zero => simpa using WordPartition.nil (p 0)
  | succ n ih =>
    rw [List.ofFn_succ]
    refine .cons (hl 0) (hr 0) ?_
    exact ih (fun i => ws i.succ) (fun j => p (j + 1))
      (fun i => hl i.succ) (fun i => hr i.succ)

private theorem zip_ofFn {α β : Type*} {n : ℕ} (u : Fin n → α) (v : Fin n → β) :
    (List.ofFn u).zip (List.ofFn v) = List.ofFn (fun i => (u i, v i)) := by
  induction n with
  | zero => simp
  | succ n ih => simp only [List.ofFn_succ, List.zip_cons_cons, ih]

/-- Every actual dyadic PL interval element admits finite paired complete
binary partitions on which its branches are affine chart identifications. -/
theorem exists_branch_wordPartitions (f : F) :
    ∃ us vs : List (List Bool),
      WordPartition 0 1 us ∧ WordPartition 0 1 vs ∧
      us.length = vs.length ∧
      ∀ u v, (u, v) ∈ us.zip vs → HasBranch f.1 u v := by
  classical
  obtain ⟨N, B, hf⟩ := f.property.1.2.1
  let L := N + B
  have hcell (i : Fin (2 ^ L)) := fine_cell_branch f hf i.val i.isLt
  choose u v hu0 hu1 hb using hcell
  refine ⟨List.ofFn u, List.ofFn v, ?_, ?_, by simp, ?_⟩
  · have h := WordPartition.ofFn u (fun j => gridPt 2 L j) hu0 hu1
    simpa [gridPt] using h
  · have hv0 (i : Fin (2 ^ L)) : chart (v i) 0 = f.1 (gridPt 2 L i.val) := by
      rw [← hu0 i]
      exact (hb i 0 (by constructor <;> norm_num)).symm
    have hv1 (i : Fin (2 ^ L)) : chart (v i) 1 = f.1 (gridPt 2 L (i.val + 1)) := by
      rw [← hu1 i]
      exact (hb i 1 (by constructor <;> norm_num)).symm
    have h := WordPartition.ofFn v (fun j => f.1 (gridPt 2 L j)) hv0 hv1
    simpa [gridPt, compactF_fix_nonpos f.property le_rfl,
      compactF_fix_one f.property le_rfl] using h
  · intro a b hab
    rw [zip_ofFn, List.mem_ofFn] at hab
    obtain ⟨i, hi⟩ := hab
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hi
    exact hb i

end Kourovka.P21_38

#audit_axioms Kourovka.P21_38.exists_branch_wordPartitions
#audit_axioms Kourovka.P21_38.exists_eventual_grid_branches
