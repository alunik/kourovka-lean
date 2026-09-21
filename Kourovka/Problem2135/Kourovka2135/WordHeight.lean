import Kourovka2135.WordCalculus
import Mathlib.Data.Finset.Max

/-!
# Height, full subtrees and the defect of outer words

These are statements about the ordered binary trees representing outer words.
`FullAt w H i` records a derived subtree at the level determined by the ambient
height budget `H`; it does not identify occurrences at different depths.
-/

set_option autoImplicit false

namespace Kourovka2135.OuterWord

@[simp]
theorem height_eq_zero_iff (w : OuterWord) : w.height = 0 ↔ w = leaf := by
  cases w with
  | leaf => simp
  | bracket l r => simp [height]

theorem Refines.height_le {v w : OuterWord} (h : Refines v w) :
    w.height ≤ v.height := by
  induction h with
  | leaf => exact Nat.zero_le _
  | bracket hl hr ihl ihr =>
      exact Nat.add_le_add_right (max_le_max ihl ihr) 1

/-- Complete every branch to the same prescribed height. -/
theorem derivedWord_refines_of_height_le (w : OuterWord) (k : ℕ)
    (hw : w.height ≤ k) : Refines (derivedWord k) w := by
  induction k generalizing w with
  | zero =>
      have hw' : w = leaf := (height_eq_zero_iff w).mp (Nat.eq_zero_of_le_zero hw)
      subst w
      exact .leaf _
  | succ k ih =>
      cases w with
      | leaf => exact .leaf _
      | bracket l r =>
          have hmax : max l.height r.height ≤ k := Nat.le_of_succ_le_succ hw
          exact .bracket
            (ih l ((Nat.le_max_left _ _).trans hmax))
            (ih r ((Nat.le_max_right _ _).trans hmax))

/-- A copy of `δᵢ` whose root lies exactly `H - i` edges below the root of w. -/
inductive FullAt : OuterWord → ℕ → ℕ → Prop where
  | here (i : ℕ) : FullAt (derivedWord i) i i
  | left {l r : OuterWord} {H i : ℕ} :
      FullAt l H i → FullAt (bracket l r) (H + 1) i
  | right {l r : OuterWord} {H i : ℕ} :
      FullAt r H i → FullAt (bracket l r) (H + 1) i

theorem FullAt.level_le {w : OuterWord} {H i : ℕ} (h : FullAt w H i) : i ≤ H := by
  induction h with
  | here => exact le_rfl
  | left _ ih => omega
  | right _ ih => omega

theorem FullAt.constituent {w : OuterWord} {H i : ℕ} (h : FullAt w H i) :
    Constituent (derivedWord i) w := by
  induction h with
  | here => exact .refl _
  | left _ ih => exact .left ih
  | right _ ih => exact .right ih

@[simp]
theorem FullAt.at_top_iff (w : OuterWord) (H : ℕ) :
    FullAt w H H ↔ w = derivedWord H := by
  constructor
  · intro h
    cases h with
    | here => rfl
    | left h => have := h.level_le; omega
    | right h => have := h.level_le; omega
  · rintro rfl
    exact .here _

theorem FullAt.constituent_child {l r : OuterWord} {H i : ℕ}
    (h : FullAt (bracket l r) H i) (hi : i < H) :
    Constituent (derivedWord i) l ∨ Constituent (derivedWord i) r := by
  generalize hw : bracket l r = w at h
  cases h with
  | here => omega
  | left h =>
      obtain ⟨rfl, rfl⟩ := bracket.inj hw
      exact Or.inl h.constituent
  | right h =>
      obtain ⟨rfl, rfl⟩ := bracket.inj hw
      exact Or.inr h.constituent

/-- A longest branch in every non-leaf tree contains a height-one full subtree
at the level determined by the tree's actual height. -/
theorem fullAt_one_of_height_pos (w : OuterWord) (hw : 0 < w.height) :
    FullAt w w.height 1 := by
  induction w with
  | leaf => simp at hw
  | bracket l r ihl ihr =>
      by_cases hm : max l.height r.height = 0
      · have hl : l = leaf := (height_eq_zero_iff l).mp (by omega)
        have hr : r = leaf := (height_eq_zero_iff r).mp (by omega)
        subst l
        subst r
        exact .here 1
      · by_cases hlr : l.height ≤ r.height
        · have hr : 0 < r.height := by omega
          simpa only [height_bracket, max_eq_right hlr] using
            (FullAt.right (l := l) (ihr hr))
        · have hl : 0 < l.height := by omega
          simpa only [height_bracket, max_eq_left (by omega : r.height ≤ l.height)] using
            (FullAt.left (r := r) (ihl hl))

/-- Choose the greatest aligned full-subtree level. -/
theorem exists_max_fullAt (w : OuterWord) (hw : 0 < w.height) :
    ∃ i, 1 ≤ i ∧ FullAt w w.height i ∧
      ∀ j, FullAt w w.height j → j ≤ i := by
  classical
  let S := (Finset.range (w.height + 1)).filter (FullAt w w.height)
  have h1 : 1 ∈ S := by
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (by omega), fullAt_one_of_height_pos w hw⟩
  have hS : S.Nonempty := ⟨1, h1⟩
  refine ⟨S.max' hS, S.le_max' 1 h1, ?_, ?_⟩
  · exact (Finset.mem_filter.mp (S.max'_mem hS)).2
  · intro j hj
    apply S.le_max' j
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by have := hj.level_le; omega), hj⟩

/-- For a non-full tree, the greatest aligned full-subtree level is below the
root, and the next level contains no aligned full subtree. -/
theorem exists_max_fullAt_lt (w : OuterWord) (hw : 0 < w.height)
    (hne : w ≠ derivedWord w.height) :
    ∃ i, 1 ≤ i ∧ i < w.height ∧ FullAt w w.height i ∧
      (∀ j, FullAt w w.height j → j ≤ i) ∧
      ¬ FullAt w w.height (i + 1) := by
  obtain ⟨i, hi, hfull, hmax⟩ := exists_max_fullAt w hw
  have hlt : i < w.height := by
    have hle := hfull.level_le
    have hni : i ≠ w.height := by
      rintro rfl
      exact hne ((FullAt.at_top_iff w _).mp hfull)
    omega
  refine ⟨i, hi, hlt, hfull, hmax, ?_⟩
  intro hnext
  have := hmax (i + 1) hnext
  omega

/-- The number of vertices, including both leaves and bracket nodes. -/
def nodeCount : OuterWord → ℕ
  | leaf => 1
  | bracket l r => l.nodeCount + r.nodeCount + 1

@[simp]
theorem nodeCount_leaf : leaf.nodeCount = 1 := rfl

@[simp]
theorem nodeCount_bracket (l r : OuterWord) :
    (bracket l r).nodeCount = l.nodeCount + r.nodeCount + 1 := rfl

theorem one_le_nodeCount (w : OuterWord) : 1 ≤ w.nodeCount := by
  cases w <;> simp only [nodeCount] <;> omega

@[simp]
theorem nodeCount_eq_one_iff (w : OuterWord) : w.nodeCount = 1 ↔ w = leaf := by
  cases w with
  | leaf => simp
  | bracket l r =>
      have hl := one_le_nodeCount l
      have hr := one_le_nodeCount r
      simp only [nodeCount_bracket, reduceCtorEq, iff_false]
      omega

theorem nodeCount_derivedWord_add_one (k : ℕ) :
    (derivedWord k).nodeCount + 1 = 2 ^ (k + 1) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change (derivedWord k).nodeCount + (derivedWord k).nodeCount + 1 + 1 =
        2 ^ (k + 1 + 1)
      rw [pow_succ]
      omega

@[simp]
theorem nodeCount_derivedWord (k : ℕ) :
    (derivedWord k).nodeCount = 2 ^ (k + 1) - 1 := by
  have := nodeCount_derivedWord_add_one k
  omega

/-- The full tree is a vertex-count upper bound for every tree of bounded height. -/
theorem nodeCount_add_one_le_pow (w : OuterWord) (k : ℕ) (hw : w.height ≤ k) :
    w.nodeCount + 1 ≤ 2 ^ (k + 1) := by
  induction k generalizing w with
  | zero =>
      have hw' : w = leaf := (height_eq_zero_iff w).mp (Nat.eq_zero_of_le_zero hw)
      subst w
      decide
  | succ k ih =>
      cases w with
      | leaf =>
          have hp : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
          change 1 + 1 ≤ 2 ^ (k + 1 + 1)
          rw [pow_succ]
          omega
      | bracket l r =>
          have hmax : max l.height r.height ≤ k := Nat.le_of_succ_le_succ hw
          have hl := ih l ((Nat.le_max_left _ _).trans hmax)
          have hr := ih r ((Nat.le_max_right _ _).trans hmax)
          change l.nodeCount + r.nodeCount + 1 + 1 ≤ 2 ^ (k + 1 + 1)
          rw [pow_succ]
          omega

theorem nodeCount_le_of_height_le (w : OuterWord) (k : ℕ) (hw : w.height ≤ k) :
    w.nodeCount ≤ 2 ^ (k + 1) - 1 := by
  have := nodeCount_add_one_le_pow w k hw
  omega

/-- Equality in the full-tree vertex bound characterizes the derived word. -/
theorem nodeCount_add_one_eq_pow_iff (w : OuterWord) (k : ℕ) (hw : w.height ≤ k) :
    w.nodeCount + 1 = 2 ^ (k + 1) ↔ w = derivedWord k := by
  constructor
  · intro hc
    induction k generalizing w with
    | zero => exact (height_eq_zero_iff w).mp (Nat.eq_zero_of_le_zero hw)
    | succ k ih =>
        cases w with
        | leaf =>
            have hp : 1 ≤ 2 ^ k := Nat.one_le_two_pow
            change 1 + 1 = 2 ^ (k + 1 + 1) at hc
            rw [pow_succ, pow_succ] at hc
            omega
        | bracket l r =>
            have hmax : max l.height r.height ≤ k := Nat.le_of_succ_le_succ hw
            have hl : l.height ≤ k := (Nat.le_max_left _ _).trans hmax
            have hr : r.height ≤ k := (Nat.le_max_right _ _).trans hmax
            have hcl := nodeCount_add_one_le_pow l k hl
            have hcr := nodeCount_add_one_le_pow r k hr
            change l.nodeCount + r.nodeCount + 1 + 1 = 2 ^ (k + 1 + 1) at hc
            rw [pow_succ] at hc
            have hleq : l = derivedWord k := ih l hl (by omega)
            have hreq : r = derivedWord k := ih r hr (by omega)
            simp only [hleq, hreq, derivedWord_succ]
  · rintro rfl
    exact nodeCount_derivedWord_add_one k

theorem nodeCount_eq_full_iff (w : OuterWord) (k : ℕ) (hw : w.height ≤ k) :
    w.nodeCount = 2 ^ (k + 1) - 1 ↔ w = derivedWord k := by
  have hp : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
  have hiff := nodeCount_add_one_eq_pow_iff w k hw
  constructor
  · intro h
    exact hiff.mp (by omega)
  · intro h
    have := hiff.mpr h
    omega

theorem Refines.nodeCount_le {v w : OuterWord} (h : Refines v w) :
    w.nodeCount ≤ v.nodeCount := by
  induction h with
  | leaf => exact one_le_nodeCount _
  | bracket hl hr ihl ihr =>
      simp only [nodeCount_bracket]
      omega

/-- A leaf refinement with unchanged vertex count has changed no leaf. -/
theorem Refines.eq_of_nodeCount_eq {v w : OuterWord} (h : Refines v w)
    (hc : v.nodeCount = w.nodeCount) : v = w := by
  induction h with
  | leaf v => exact (nodeCount_eq_one_iff v).mp hc
  | @bracket vl vr wl wr hl hr ihl ihr =>
      have hcl := hl.nodeCount_le
      have hcr := hr.nodeCount_le
      simp only [nodeCount_bracket] at hc
      have hleq := ihl (by omega)
      have hreq := ihr (by omega)
      exact congrArg₂ OuterWord.bracket hleq hreq

theorem Refines.nodeCount_lt_of_ne {v w : OuterWord} (h : Refines v w)
    (hne : v ≠ w) : w.nodeCount < v.nodeCount := by
  have hle := h.nodeCount_le
  have hne' : v.nodeCount ≠ w.nodeCount := fun hc => hne (h.eq_of_nodeCount_eq hc)
  omega

/-- The vertices missing from the full tree of the same height. -/
def defect (w : OuterWord) : ℕ := 2 ^ (w.height + 1) - 1 - w.nodeCount

@[simp]
theorem defect_eq_zero_iff (w : OuterWord) :
    w.defect = 0 ↔ w = derivedWord w.height := by
  have hb := nodeCount_le_of_height_le w w.height le_rfl
  have heq := nodeCount_eq_full_iff w w.height le_rfl
  unfold defect
  constructor
  · intro hd
    exact heq.mp (by omega)
  · intro hw
    have := heq.mpr hw
    omega

@[simp]
theorem defect_derivedWord (k : ℕ) : (derivedWord k).defect = 0 := by
  apply (defect_eq_zero_iff _).mpr
  simp only [height_derivedWord]

/-- A proper refinement that preserves the root's height. -/
def ProperSameHeightExtension (v w : OuterWord) : Prop :=
  Refines v w ∧ v.height = w.height ∧ v ≠ w

theorem ProperSameHeightExtension.defect_lt {v w : OuterWord}
    (h : ProperSameHeightExtension v w) : v.defect < w.defect := by
  obtain ⟨hr, hh, hne⟩ := h
  have hc := hr.nodeCount_lt_of_ne hne
  have hv := nodeCount_le_of_height_le v w.height hh.le
  have hw := nodeCount_le_of_height_le w w.height le_rfl
  unfold defect
  rw [hh]
  omega

end Kourovka2135.OuterWord
