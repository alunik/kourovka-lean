import Kourovka.Problems.P21_38.Proof.BinaryBranches
import Mathlib.Data.List.Pairwise
import Kourovka.External.GroupApproximation.Meta.AxiomGuard

/-!
# Complete ordered binary partitions

`WordPartition a b ws` records consecutive standard binary intervals from `a`
to `b`. Full binary trees supply such partitions of the unit interval. Any
finite prefix-free family can be included among the leaves of a full tree.
-/

namespace Kourovka.P21_38

open BinaryWord

/-- Consecutive binary intervals, with both endpoints recorded explicitly. -/
inductive WordPartition : ℚ → ℚ → List (List Bool) → Prop
  | nil (a : ℚ) : WordPartition a a []
  | cons {a b c : ℚ} {w : List Bool} {ws : List (List Bool)}
      (left : chart w 0 = a) (right : chart w 1 = c)
      (tail : WordPartition c b ws) : WordPartition a b (w :: ws)

namespace WordPartition

theorem append {a b c : ℚ} {us vs : List (List Bool)}
    (hu : WordPartition a b us) (hv : WordPartition b c vs) :
    WordPartition a c (us ++ vs) := by
  induction hu with
  | nil => exact hv
  | cons hl hr ht ih => exact .cons hl hr (ih hv)

/-- Prefixing all words transports a partition through the prefix chart. -/
theorem prefixWords (u : List Bool) {a b : ℚ} {ws : List (List Bool)}
    (h : WordPartition a b ws) :
    WordPartition (chart u a) (chart u b) (ws.map (u ++ ·)) := by
  induction h with
  | nil => exact .nil _
  | cons hl hr ht ih =>
    exact .cons (by simp only [chart_append, hl])
      (by simp only [chart_append, hr]) ih

theorem le {a b : ℚ} {ws : List (List Bool)} (h : WordPartition a b ws) : a ≤ b := by
  induction h with
  | nil => exact le_rfl
  | @cons a b c w ws hl hr ht ih =>
    have hw := chart_strictMono w (show (0 : ℚ) < 1 by norm_num)
    rw [hl, hr] at hw
    exact hw.le.trans ih

theorem mem_bounds {a b : ℚ} {ws : List (List Bool)} (h : WordPartition a b ws)
    {w : List Bool} (hw : w ∈ ws) : a ≤ chart w 0 ∧ chart w 1 ≤ b := by
  induction h with
  | nil => simp at hw
  | @cons a b c v vs hl hr ht ih =>
    rcases List.mem_cons.mp hw with rfl | hw
    · exact ⟨hl.ge, hr.le.trans ht.le⟩
    · obtain ⟨hleft, hright⟩ := ih hw
      have hvc := chart_strictMono v (show (0 : ℚ) < 1 by norm_num)
      rw [hl, hr] at hvc
      exact ⟨hvc.le.trans hleft, hright⟩

/-- The intervals are ordered and have disjoint interiors. -/
theorem ordered {a b : ℚ} {ws : List (List Bool)} (h : WordPartition a b ws) :
    ws.Pairwise (fun u v => chart u 1 ≤ chart v 0) := by
  induction h with
  | nil => exact .nil
  | cons hl hr ht ih =>
    apply List.pairwise_cons.mpr
    refine ⟨?_, ih⟩
    intro v hv
    exact hr.le.trans (ht.mem_bounds hv).1

/-- Every point of a nonempty partition belongs to one of its closed intervals. -/
theorem covers {a b : ℚ} {ws : List (List Bool)} (h : WordPartition a b ws)
    (hne : ws ≠ []) {t : ℚ} (hta : a ≤ t) (htb : t ≤ b) :
    ∃ w ∈ ws, chart w 0 ≤ t ∧ t ≤ chart w 1 := by
  induction h with
  | nil => exact (hne rfl).elim
  | @cons a b c w ws hl hr ht ih =>
    by_cases htc : t ≤ c
    · exact ⟨w, List.mem_cons_self, hl ▸ hta, hr ▸ htc⟩
    · have hws : ws ≠ [] := by
        intro heq
        subst ws
        cases ht
        exact htc htb
      obtain ⟨v, hv, hleft, hright⟩ := ih hws (le_of_not_ge htc) htb
      exact ⟨v, List.mem_cons_of_mem _ hv, hleft, hright⟩

end WordPartition

/-- A finite full binary tree. -/
inductive BinaryTree
  | leaf
  | node (left right : BinaryTree)
  deriving DecidableEq

namespace BinaryTree

/-- The ordered binary addresses of the leaves. -/
def leaves : BinaryTree → List (List Bool)
  | leaf => [[]]
  | node l r => l.leaves.map (false :: ·) ++ r.leaves.map (true :: ·)

@[simp] theorem leaves_leaf : leaves leaf = [[]] := rfl

@[simp] theorem leaves_node (l r : BinaryTree) :
    (node l r).leaves = l.leaves.map (false :: ·) ++ r.leaves.map (true :: ·) := rfl

theorem leaves_ne_nil (T : BinaryTree) : T.leaves ≠ [] := by
  induction T with
  | leaf => simp
  | node l r hl hr => simp [hl, hr]

/-- Leaf intervals form a complete ordered partition of the unit interval. -/
theorem leaves_partition (T : BinaryTree) : WordPartition 0 1 T.leaves := by
  induction T with
  | leaf => exact .cons rfl rfl (.nil 1)
  | node l r hl hr =>
    have hleft := hl.prefixWords [false]
    have hright := hr.prefixWords [true]
    have hleft' : WordPartition 0 (1 / 2) (l.leaves.map (false :: ·)) := by
      simpa [chart] using hleft
    have hright' : WordPartition (1 / 2) 1 (r.leaves.map (true :: ·)) := by
      simpa [chart] using hright
    exact hleft'.append hright'

theorem leaves_ordered (T : BinaryTree) :
    T.leaves.Pairwise (fun u v => chart u 1 ≤ chart v 0) := T.leaves_partition.ordered

theorem leaves_cover (T : BinaryTree) {t : ℚ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∃ w ∈ T.leaves, chart w 0 ≤ t ∧ t ≤ chart w 1 :=
  T.leaves_partition.covers T.leaves_ne_nil ht0 ht1

@[simp] theorem cons_mem_leaves_node (b : Bool) (w : List Bool) (l r : BinaryTree) :
    b :: w ∈ (node l r).leaves ↔ if b then w ∈ r.leaves else w ∈ l.leaves := by
  cases b <;> simp [leaves]

/-- Make a prescribed address a leaf. Existing leaves at incomparable
addresses remain in place; any subtree at this address is pruned. -/
def insertLeaf : BinaryTree → List Bool → BinaryTree
  | _, [] => leaf
  | leaf, false :: w => node (insertLeaf leaf w) leaf
  | leaf, true :: w => node leaf (insertLeaf leaf w)
  | node l r, false :: w => node (insertLeaf l w) r
  | node l r, true :: w => node l (insertLeaf r w)

theorem mem_leaves_insertLeaf (T : BinaryTree) (w : List Bool) :
    w ∈ (T.insertLeaf w).leaves := by
  induction w generalizing T with
  | nil => simp [insertLeaf]
  | cons b w ih => cases T <;> cases b <;> simp [insertLeaf, ih]

/-- Inserting one leaf preserves every existing incomparable leaf. -/
theorem mem_leaves_insertLeaf_of_incomparable {T : BinaryTree} {u w : List Bool}
    (hu : u ∈ T.leaves) (huw : ¬ u <+: w) (hwu : ¬ w <+: u) :
    u ∈ (T.insertLeaf w).leaves := by
  induction w generalizing T u with
  | nil => exact (hwu List.nil_prefix).elim
  | cons b w ih =>
    cases u with
    | nil => exact (huw List.nil_prefix).elim
    | cons c u =>
      cases T with
      | leaf => simp [leaves] at hu
      | node l r =>
        cases b <;> cases c
        · simp only [cons_mem_leaves_node, Bool.false_eq_true, ↓reduceIte] at hu
          simpa only [insertLeaf, cons_mem_leaves_node, Bool.false_eq_true, ↓reduceIte] using
            ih hu (by simpa using huw) (by simpa using hwu)
        · simpa only [insertLeaf, cons_mem_leaves_node, ↓reduceIte] using hu
        · simpa only [insertLeaf, cons_mem_leaves_node, Bool.false_eq_true, ↓reduceIte] using hu
        · simp only [cons_mem_leaves_node, ↓reduceIte] at hu
          simpa only [insertLeaf, cons_mem_leaves_node, ↓reduceIte] using
            ih hu (by simpa using huw) (by simpa using hwu)

/-- Every finite prefix-free list occurs among the leaves of a full binary tree.
Extra leaves complete the partition outside the prescribed intervals. -/
theorem exists_leaves_containing (ws : List (List Bool))
    (hfree : ws.Pairwise (fun u v => ¬ u <+: v ∧ ¬ v <+: u)) :
    ∃ T : BinaryTree, ∀ w ∈ ws, w ∈ T.leaves := by
  induction ws with
  | nil => exact ⟨leaf, by simp⟩
  | cons w ws ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hfree
    obtain ⟨T, hT⟩ := ih htail
    refine ⟨T.insertLeaf w, ?_⟩
    intro u hu
    rcases List.mem_cons.mp hu with rfl | hu
    · exact T.mem_leaves_insertLeaf _
    · exact mem_leaves_insertLeaf_of_incomparable (hT u hu) (hhead u hu).2 (hhead u hu).1

end BinaryTree

/-- A finite prefix-free family can be completed to an ordered binary partition. -/
theorem exists_wordPartition_containing (ws : List (List Bool))
    (hfree : ws.Pairwise (fun u v => ¬ u <+: v ∧ ¬ v <+: u)) :
    ∃ ps : List (List Bool), WordPartition 0 1 ps ∧ ∀ w ∈ ws, w ∈ ps := by
  obtain ⟨T, hT⟩ := BinaryTree.exists_leaves_containing ws hfree
  exact ⟨T.leaves, T.leaves_partition, hT⟩

end Kourovka.P21_38

#audit_axioms Kourovka.P21_38.BinaryTree.leaves_partition
#audit_axioms Kourovka.P21_38.BinaryTree.leaves_cover
#audit_axioms Kourovka.P21_38.BinaryTree.exists_leaves_containing
#audit_axioms Kourovka.P21_38.exists_wordPartition_containing
