import Kourovka.Problems.P21_38.Proof.BinaryPartitions

/-!
# Binary prefixes and interval order

Overlapping interiors of standard binary intervals force comparable words.
Consequently a sufficiently long word lies below a leaf of any complete
finite binary partition.
-/

namespace Kourovka.P21_38

namespace BinaryWord

/-- Two binary intervals with overlapping interiors have comparable addresses. -/
theorem prefix_comparable_of_overlap {u v : List Bool}
    (huv : chart u 0 < chart v 1) (hvu : chart v 0 < chart u 1) :
    u <+: v ∨ v <+: u := by
  induction u generalizing v with
  | nil => exact Or.inl List.nil_prefix
  | cons a u ih =>
    cases v with
    | nil => exact Or.inr List.nil_prefix
    | cons b v =>
      by_cases hab : a = b
      · subst b
        have h0 : chart u 0 < chart v 1 := by
          simp only [chart_cons] at huv
          linarith
        have h1 : chart v 0 < chart u 1 := by
          simp only [chart_cons] at hvu
          linarith
        rcases ih h0 h1 with h | h
        · obtain ⟨s, rfl⟩ := h
          exact Or.inl ⟨s, rfl⟩
        · obtain ⟨s, rfl⟩ := h
          exact Or.inr ⟨s, rfl⟩
      · have hu0 := (chart_mem_unit u (show (0 : ℚ) ∈ Set.Icc 0 1 by norm_num)).1
        have hu1 := (chart_mem_unit u (show (1 : ℚ) ∈ Set.Icc 0 1 by norm_num)).2
        have hv0 := (chart_mem_unit v (show (0 : ℚ) ∈ Set.Icc 0 1 by norm_num)).1
        have hv1 := (chart_mem_unit v (show (1 : ℚ) ∈ Set.Icc 0 1 by norm_num)).2
        cases a <;> cases b <;> simp_all [chart_cons] <;> linarith

theorem prefix_of_overlap_of_length_le {u v : List Bool}
    (huv : chart u 0 < chart v 1) (hvu : chart v 0 < chart u 1)
    (hlen : u.length ≤ v.length) : u <+: v := by
  rcases prefix_comparable_of_overlap huv hvu with h | h
  · exact h
  · have heq := h.eq_of_length (Nat.le_antisymm h.length_le hlen)
    exact heq ▸ List.prefix_refl _

end BinaryWord

/-- A uniform finite bound makes every binary word extend some partition leaf. -/
theorem WordPartition.exists_prefix_of_length_le {ws : List (List Bool)}
    (h : WordPartition 0 1 ws) (r : List Bool)
    (hlen : ∀ w ∈ ws, w.length ≤ r.length) :
    ∃ w ∈ ws, w <+: r := by
  have hne : ws ≠ [] := by
    intro heq
    subst ws
    cases h
  have ht : (1 / 2 : ℚ) ∈ Set.Icc 0 1 := by norm_num
  have hmid := BinaryWord.chart_mem_unit r ht
  obtain ⟨w, hw, hlow, hhigh⟩ := h.covers hne hmid.1 hmid.2
  have hr0 := BinaryWord.chart_strictMono r (show (0 : ℚ) < 1 / 2 by norm_num)
  have hr1 := BinaryWord.chart_strictMono r (show (1 / 2 : ℚ) < 1 by norm_num)
  exact ⟨w, hw, BinaryWord.prefix_of_overlap_of_length_le
    (hlow.trans_lt hr1) (hr0.trans_le hhigh) (hlen w hw)⟩

end Kourovka.P21_38
