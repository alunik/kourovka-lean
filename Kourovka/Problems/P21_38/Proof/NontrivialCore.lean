import Kourovka.Problems.P21_38.Proof.BinaryDyadic
import Kourovka.Problems.P21_38.Proof.CorePerfect
import Kourovka.Problems.P21_38.Proof.AffineBranches

/-!
# Dyadic transitivity and a nontrivial compactly supported element

Deep branch communication gives transitivity on interior dyadic points.
Conjugating a fixed point to a moved point then supplies a nontrivial
commutator, which belongs to the compact core by the proved kernel theorem.
-/

namespace Kourovka.P21_38

open GroupApproximation.HigmanThompson BinaryWord
open scoped commutatorElement

def DyadicTransitive (H : Subgroup (Equiv.Perm ℚ)) : Prop :=
  ∀ α β : ℚ, 0 < α → α < 1 → 0 < β → β < 1 →
    (∃ N, α ∈ Grid 2 N) → (∃ N, β ∈ Grid 2 N) → ∃ h ∈ H, h α = β

private theorem chart_zero_eq_zero_of_true_not_mem {w : List Bool} (h : true ∉ w) :
    chart w 0 = 0 := by
  induction w with
  | nil => rfl
  | cons b w ih => cases b <;> simp_all [chart]

theorem exists_mixed_word_at_dyadic {α : ℚ} (hα0 : 0 < α) (hα1 : α < 1)
    (hgrid : ∃ N, α ∈ Grid 2 N) :
    ∃ u : List Bool, false ∈ u ∧ true ∈ u ∧ chart u 0 = α := by
  obtain ⟨N, hgrid⟩ := hgrid
  obtain ⟨w, _, hw⟩ := exists_chart_zero_of_grid hα0.le hα1 hgrid
  have hw1 : true ∈ w := by
    by_contra h
    have hzero := chart_zero_eq_zero_of_true_not_mem h
    rw [hw] at hzero
    linarith
  exact ⟨w ++ [false], by simp, List.mem_append_left _ hw1, by simp [chart_append, chart, hw]⟩

/-- The eventual branch relation suffices for transitivity on all interior dyadic points. -/
theorem dyadicTransitive_of_deep_branches {H : Subgroup (Equiv.Perm ℚ)}
    (hdeep : ∀ u v : List Bool, false ∈ u → true ∈ u → false ∈ v → true ∈ v →
      ∃ N : ℕ, ∀ s t : List Bool, N ≤ s.length → N ≤ t.length →
        BranchRelated H (u ++ s) (v ++ t)) : DyadicTransitive H := by
  intro α β hα0 hα1 hβ0 hβ1 hα hβ
  obtain ⟨u, hu0, hu1, hu⟩ := exists_mixed_word_at_dyadic hα0 hα1 hα
  obtain ⟨v, hv0, hv1, hv⟩ := exists_mixed_word_at_dyadic hβ0 hβ1 hβ
  obtain ⟨N, hN⟩ := hdeep u v hu0 hu1 hv0 hv1
  obtain ⟨h, hh, hb⟩ := hN (List.replicate N false) (List.replicate N false) (by simp) (by simp)
  refine ⟨h, hh, ?_⟩
  have heq := hb 0 (by norm_num)
  simpa [chart_append, chart_replicate_false, hu, hv] using heq

/-- Moving a fixed dyadic point to a moved dyadic point forces a nontrivial commutator. -/
theorem exists_nontrivial_core_of_fixed_and_moved
    {H : Subgroup (Equiv.Perm ℚ)} (hH : H ≤ compactF 0 1) (htrans : DyadicTransitive H)
    {g : Equiv.Perm ℚ} (hg : g ∈ H) {α β : ℚ}
    (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hα : ∃ N, α ∈ Grid 2 N) (hβ : ∃ N, β ∈ Grid 2 N)
    (hfix : g α = α) (hmove : g β ≠ β) :
    ∃ h ∈ H, h ∈ compactCore 0 ∧ h ≠ 1 := by
  obtain ⟨k, hk, hkab⟩ := htrans α β hα0 hα1 hβ0 hβ1 hα hβ
  refine ⟨⁅g, k⁆, ?_, ?_, ?_⟩
  · exact H.mul_mem (H.mul_mem (H.mul_mem hg hk) (H.inv_mem hg)) (H.inv_mem hk)
  · rw [compactCore_eq_ambient_commutator]
    exact Subgroup.commutator_mem_commutator (hH hg) (hH hk)
  · intro hcomm
    have hmul : g * k = k * g := by
      have h := congrArg (fun x : Equiv.Perm ℚ => x * k * g) hcomm
      simpa [commutatorElement_def, mul_assoc] using h
    have h := congrArg (fun x : Equiv.Perm ℚ => x α) hmul
    simp only [Equiv.Perm.mul_apply, hkab, hfix] at h
    exact hmove h

#audit_axioms dyadicTransitive_of_deep_branches
#audit_axioms exists_nontrivial_core_of_fixed_and_moved

/-- A local branch shift fixes one interior dyadic point and moves another. -/
theorem exists_nontrivial_core_of_shift
    {H : Subgroup (Equiv.Perm ℚ)} (hH : H ≤ compactF 0 1) (htrans : DyadicTransitive H)
    {g : Equiv.Perm ℚ} (hg : g ∈ H) {u : List Bool}
    (hu0 : 0 < chart u 0) (hu1 : chart u 1 < 1)
    (hshift : HasBranch g (u ++ [false]) u) :
    ∃ h ∈ H, h ∈ compactCore 0 ∧ h ≠ 1 := by
  have hmid : chart (u ++ [false]) 1 = chart u (1 / 2) := by simp [chart_append, chart]
  have hm0 : 0 < chart (u ++ [false]) 1 := by
    rw [hmid]
    exact hu0.trans ((chart_strictMono u) (by norm_num))
  have hm1 : chart (u ++ [false]) 1 < 1 := by
    rw [hmid]
    exact ((chart_strictMono u) (by norm_num)).trans hu1
  have hfix : g (chart u 0) = chart u 0 := by
    simpa [chart_append, chart] using hshift 0 (by norm_num)
  have hmove : g (chart (u ++ [false]) 1) ≠ chart (u ++ [false]) 1 := by
    rw [hshift 1 (by norm_num), hmid]
    exact (chart_strictMono u (show (1 / 2 : ℚ) < 1 by norm_num)).ne'
  exact exists_nontrivial_core_of_fixed_and_moved hH htrans hg hu0
    ((chart_strictMono u (show (0 : ℚ) < 1 by norm_num)).trans hu1) hm0 hm1
    (chart_zero_dyadic u) (chart_one_dyadic _) hfix hmove

#audit_axioms exists_nontrivial_core_of_shift

end Kourovka.P21_38
