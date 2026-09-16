import Kourovka.Problems.P21_38.Proof.FixerMotion
import Kourovka.Problems.P21_38.Proof.NontrivialCore

/-!
# Compression into an interior interval

First move a dyadic point beyond the requested compact interval below the
target endpoint. The fixer of that endpoint then moves the left endpoint
past the target's left edge without crossing its right edge.
-/

namespace Kourovka.P21_38

open GroupApproximation.HigmanThompson BinaryWord Set

/-- Every compact interior rational interval can be compressed into any
positive interior target with a dyadic right endpoint. -/
theorem exists_interval_compression_of_deep_branches
    {H : Subgroup (Equiv.Perm ℚ)} (hH : H ≤ compactF 0 1)
    (hdeep : DeepBranchCommunication H)
    (hcore : ∃ g ∈ H, g ∈ compactCore 0 ∧ g ≠ 1)
    {a b α β : ℚ} (ha : 0 < a) (hb : b < 1)
    (hα : 0 < α) (hαβ : α < β) (hβ : β < 1)
    (hβgrid : ∃ N : ℕ, β ∈ Grid 2 N) :
    ∃ q ∈ H, MapsTo q (Icc a b) (Ioo α β) := by
  have htrans : DyadicTransitive H := dyadicTransitive_of_deep_branches
    (fun u v hu0 hu1 hv0 hv1 => hdeep u v ⟨hu0, hu1⟩ ⟨hv0, hv1⟩)
  obtain ⟨b', hbb', hb'1, hb'grid⟩ := exists_grid_mem_Ioo (m := 0)
    (show max b 0 < (1 : ℚ) from max_lt hb zero_lt_one)
  have hb'0 : 0 < b' := (le_max_right _ _).trans_lt hbb'
  have hbb' : b < b' := (le_max_left _ _).trans_lt hbb'
  obtain ⟨γ, hαγ, hγβ, hγgrid⟩ := exists_grid_mem_Ioo (m := 0) hαβ
  obtain ⟨f, hfH, hfb'⟩ := htrans b' γ hb'0 hb'1 (hα.trans hαγ)
    (hγβ.trans hβ) hb'grid hγgrid
  have hfmono := compactF_strictMono (hH hfH)
  have hfa : 0 < f a := by
    have h := hfmono ha
    rwa [compactF_fix_nonpos (hH hfH) le_rfl] at h
  have hfb : f b < β := by
    have h := hfmono hbb'
    rw [hfb'] at h
    exact h.trans hγβ
  obtain ⟨u, _, _, hu⟩ := exists_mixed_word_at_dyadic (hα.trans hαβ) hβ hβgrid
  have hcuts : NoInvariantRealCut (wordFixer H u) 0 β := by
    rw [← hu]
    exact wordFixer_noInvariantRealCut_of_deep_branches hH hdeep hcore u
  have hmono : ∀ k ∈ wordFixer H u, StrictMono k :=
    fun k hk => compactF_strictMono (hH hk.1)
  have hfix : ∀ k ∈ wordFixer H u, k β = β := by
    intro k hk
    rw [← hu]
    exact hk.2.left_endpoint
  obtain ⟨k, hk, hkmap⟩ := rational_interval_compression (wordFixer H u)
    hmono hcuts hfix hfa hfb hαβ
  refine ⟨k * f, H.mul_mem hk.1 hfH, ?_⟩
  intro t ht
  exact hkmap ⟨hfmono.monotone ht.1, hfmono.monotone ht.2⟩

/-- The binary-interval specialization used to place a compact interval in
the interval immediately preceding a local branch shift. -/
theorem exists_interval_compression_to_binary
    {H : Subgroup (Equiv.Perm ℚ)} (hH : H ≤ compactF 0 1)
    (hdeep : DeepBranchCommunication H)
    (hcore : ∃ g ∈ H, g ∈ compactCore 0 ∧ g ≠ 1)
    {a b : ℚ} (ha : 0 < a) (hb : b < 1)
    (v : List Bool) (hv0 : 0 < chart v 0) (hv1 : chart v 1 < 1) :
    ∃ q ∈ H, MapsTo q (Icc a b) (Icc (chart v 0) (chart v 1)) := by
  obtain ⟨q, hq, hmap⟩ := exists_interval_compression_of_deep_branches
    hH hdeep hcore ha hb hv0 (chart_zero_lt_one v) hv1 (chart_one_dyadic v)
  exact ⟨q, hq, fun t ht => ⟨(hmap ht).1.le, (hmap ht).2.le⟩⟩

#audit_axioms exists_interval_compression_of_deep_branches
#audit_axioms exists_interval_compression_to_binary

end Kourovka.P21_38
