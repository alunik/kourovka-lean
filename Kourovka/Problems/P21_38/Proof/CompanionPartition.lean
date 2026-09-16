import Kourovka.Problems.P21_38.Proof.BinaryPartitions

/-!
# A source partition for the generating companion

Three strictly separated interior binary intervals can be included in an
ordered complete partition with the endpoint and refinement pattern required
by the companion construction.
-/

namespace Kourovka.P21_38

open BinaryWord

namespace WordPartition

theorem nil_endpoints {a b : ℚ} (h : WordPartition a b []) : a = b := by
  cases h
  rfl

theorem first_left {a b : ℚ} {w : List Bool} {ws : List (List Bool)}
    (h : WordPartition a b (w :: ws)) : chart w 0 = a := by
  cases h with
  | cons hl hr ht => exact hl

theorem split_append {a b : ℚ} {us vs : List (List Bool)}
    (h : WordPartition a b (us ++ vs)) :
    ∃ c, WordPartition a c us ∧ WordPartition c b vs := by
  induction us generalizing a with
  | nil => exact ⟨a, .nil a, h⟩
  | cons u us ih =>
    cases h with
    | cons hl hr ht =>
      obtain ⟨c, hp, hs⟩ := ih ht
      exact ⟨c, .cons hl hr hp, hs⟩

theorem split_at_word {a b : ℚ} {ws : List (List Bool)}
    (h : WordPartition a b ws) {w : List Bool} (hw : w ∈ ws) :
    ∃ P Q, ws = P ++ w :: Q ∧
      WordPartition a (chart w 0) P ∧ WordPartition (chart w 1) b Q := by
  obtain ⟨P, Q, rfl⟩ := List.mem_iff_append.mp hw
  obtain ⟨c, hp, hq⟩ := h.split_append
  cases hq with
  | cons hl hr ht =>
    exact ⟨P, Q, rfl, by simpa only [← hl] using hp, by simpa only [← hr] using ht⟩

end WordPartition

namespace BinaryWord

theorem prefix_incomparable_of_right_le_left {u v : List Bool}
    (h : chart u 1 ≤ chart v 0) : ¬ u <+: v ∧ ¬ v <+: u := by
  constructor
  · rintro ⟨s, rfl⟩
    have hs : chart s 0 < 1 :=
      (chart_strictMono s (show (0 : ℚ) < 1 by norm_num)).trans_le
        (chart_mem_unit s (show (1 : ℚ) ∈ Set.Icc (0 : ℚ) 1 by constructor <;> norm_num)).2
    have hu := chart_strictMono u hs
    rw [chart_append] at h
    exact (not_lt_of_ge h) hu
  · rintro ⟨s, rfl⟩
    have hs' : 0 < chart s 1 :=
      lt_of_le_of_lt
        (chart_mem_unit s (show (0 : ℚ) ∈ Set.Icc (0 : ℚ) 1 by constructor <;> norm_num)).1
        (chart_strictMono s (by norm_num))
    have hv := chart_strictMono v hs'
    rw [chart_append] at h
    exact (not_lt_of_ge h) hv

theorem eq_replicate_false_of_chart_zero {w : List Bool} (h : chart w 0 = 0) :
    w = List.replicate w.length false := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    have hb := (chart_mem_unit w (show (0 : ℚ) ∈ Set.Icc (0 : ℚ) 1 by constructor <;> norm_num)).1
    cases b
    · have hw : chart w 0 = 0 := by simpa using h
      change false :: w = false :: List.replicate w.length false
      exact congrArg (false :: ·) (ih hw)
    · simp only [chart_cons, ↓reduceIte] at h
      linarith

theorem eq_replicate_true_of_chart_one {w : List Bool} (h : chart w 1 = 1) :
    w = List.replicate w.length true := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    have hb := (chart_mem_unit w (show (1 : ℚ) ∈ Set.Icc (0 : ℚ) 1 by constructor <;> norm_num)).2
    cases b
    · simp only [chart_cons, Bool.false_eq_true, ↓reduceIte, zero_add] at h
      linarith
    · have hw : chart w 1 = 1 := by
        simp only [chart_cons, ↓reduceIte] at h
        linarith
      change true :: w = true :: List.replicate w.length true
      exact congrArg (true :: ·) (ih hw)

end BinaryWord

private theorem prescribed_source_prefixFree {u v w : List Bool}
    (huv : chart u 1 < chart v 0) (hvw : chart v 1 < chart w 0) :
    [u, v ++ [false], v ++ [true], w].Pairwise
      (fun p q => ¬ p <+: q ∧ ¬ q <+: p) := by
  have hmid0 : chart v 0 ≤ chart v (1 / 2) := (chart_strictMono v).monotone (by norm_num)
  have hmid1 : chart v (1 / 2) ≤ chart v 1 := (chart_strictMono v).monotone (by norm_num)
  have ho : [u, v ++ [false], v ++ [true], w].Pairwise
      (fun p q => chart p 1 ≤ chart q 0) := by
    simp only [List.pairwise_cons, List.forall_mem_cons,
      List.Pairwise.nil, and_true, chart_append, chart_cons, chart_nil,
      Bool.false_eq_true, ↓reduceIte, zero_add]
    norm_num
    exact ⟨⟨huv.le, by linarith, by linarith⟩, by linarith, hvw.le⟩
  exact ho.imp (fun h => prefix_incomparable_of_right_le_left h)

/-- The source-tree pattern needed for the companion construction. The two
endpoint leaves are nonempty pure words, and the block after `w` is nonempty. -/
theorem exists_companion_source_partition {u v w : List Bool}
    (hu0 : 0 < chart u 0) (huv : chart u 1 < chart v 0)
    (hvw : chart v 1 < chart w 0) (hw1 : chart w 1 < 1) :
    ∃ na nz : ℕ, 0 < na ∧ 0 < nz ∧ ∃ L R : List (List Bool),
      R ≠ [] ∧ u ∈ L ∧ v ++ [false] ∈ L ∧ v ++ [true] ∈ L ∧
      WordPartition 0 1
        (List.replicate na false ::
          (L ++ [w ++ [false], w ++ [true, false], w ++ [true, true]] ++
            R ++ [List.replicate nz true])) := by
  obtain ⟨ps, hps, hincl⟩ := exists_wordPartition_containing
    [u, v ++ [false], v ++ [true], w] (prescribed_source_prefixFree huv hvw)
  obtain ⟨P, Q, hseq, hP, hQ⟩ := hps.split_at_word (hincl w (by simp))
  have hupos := chart_strictMono u (show (0 : ℚ) < 1 by norm_num)
  have hvpos := chart_strictMono v (show (0 : ℚ) < 1 by norm_num)
  have hwpos := chart_strictMono w (show (0 : ℚ) < 1 by norm_num)
  have hmid0 : chart v 0 ≤ chart v (1 / 2) := (chart_strictMono v).monotone (by norm_num)
  have hmid1 : chart v (1 / 2) ≤ chart v 1 := (chart_strictMono v).monotone (by norm_num)
  have before (x : List Bool) (hx : x ∈ [u, v ++ [false], v ++ [true], w])
      (hgap : chart x 1 < chart w 0) : x ∈ P := by
    have hxps := hincl x hx
    rw [hseq, List.mem_append, List.mem_cons] at hxps
    rcases hxps with hx | heq | hx
    · exact hx
    · rw [heq] at hgap
      linarith
    · have hbounds := hQ.mem_bounds hx
      have hxpos := chart_strictMono x (show (0 : ℚ) < 1 by norm_num)
      linarith [hbounds.1]
  have huP : u ∈ P := before u (by simp) (by linarith)
  have hv0P : v ++ [false] ∈ P := before _ (by simp) (by
    simp only [chart_append, chart_cons, chart_nil, Bool.false_eq_true, ↓reduceIte, zero_add]
    norm_num
    linarith)
  have hv1P : v ++ [true] ∈ P := before _ (by simp) (by simpa [chart_append, chart] using hvw)
  have hQne : Q ≠ [] := by
    intro heq
    have hends : chart w 1 = 1 := by
      rw [heq] at hQ
      exact hQ.nil_endpoints
    linarith
  cases P with
  | nil => simp at huP
  | cons a L =>
    have ha0 : chart a 0 = 0 := hP.first_left
    have haNe : a ≠ [] := by
      intro heq
      have hbound := (hP.mem_bounds (List.mem_cons_self)).2
      rw [heq, chart_nil] at hbound
      linarith
    have after_head (x : List Bool) (hx : x ∈ a :: L) (hx0 : 0 < chart x 0) : x ∈ L := by
      rcases List.mem_cons.mp hx with heq | hx
      · rw [heq, ha0] at hx0
        exact (lt_irrefl 0 hx0).elim
      · exact hx
    have huL : u ∈ L := after_head u huP hu0
    have hv0L : v ++ [false] ∈ L := after_head _ hv0P (by
      simp [chart_append, chart]
      linarith)
    have hv1L : v ++ [true] ∈ L := after_head _ hv1P (by
      simp [chart_append, chart]
      linarith)
    obtain ⟨R, z, hQeq⟩ : ∃ R z, Q = R ++ [z] :=
      ⟨Q.dropLast, Q.getLast hQne, (List.dropLast_concat_getLast hQne).symm⟩
    rw [hQeq] at hQ
    obtain ⟨c, hR, hzpart⟩ := hQ.split_append
    have hz0 : chart z 0 = c := by
      cases hzpart with
      | cons hl hr ht => exact hl
    have hz1 : chart z 1 = 1 := by
      cases hzpart with
      | cons hl hr ht => cases ht; exact hr
    have hwthree : WordPartition (chart w 0) (chart w 1)
        [w ++ [false], w ++ [true, false], w ++ [true, true]] := by
      simpa [BinaryTree.leaves] using
        (BinaryTree.node BinaryTree.leaf (BinaryTree.node BinaryTree.leaf BinaryTree.leaf)).leaves_partition.prefixWords w
    have hztwo : WordPartition c 1 [z ++ [false], z ++ [true]] := by
      simpa [BinaryTree.leaves, hz0, hz1] using
        (BinaryTree.node BinaryTree.leaf BinaryTree.leaf).leaves_partition.prefixWords z
    have hzrep : z ++ [true] = List.replicate (z.length + 1) true := by
      calc
        z ++ [true] = List.replicate z.length true ++ [true] :=
          congrArg (fun t => t ++ [true]) (eq_replicate_true_of_chart_one hz1)
        _ = List.replicate (z.length + 1) true := List.replicate_succ'.symm
    have hfull := ((hP.append hwthree).append hR).append hztwo
    refine ⟨a.length, z.length + 1, List.length_pos_iff.mpr haNe, by omega,
      L, R ++ [z ++ [false]], by simp, huL, hv0L, hv1L, ?_⟩
    have harep := eq_replicate_false_of_chart_zero ha0
    simpa only [List.cons_append, List.nil_append, List.append_assoc, ← harep, ← hzrep] using hfull

end Kourovka.P21_38

#audit_axioms Kourovka.P21_38.exists_companion_source_partition
