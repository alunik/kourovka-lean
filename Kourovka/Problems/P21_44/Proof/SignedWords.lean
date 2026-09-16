import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-!
# Signed alternating words

The first Boolean distinguishes the two generators (false for `a`, true for
`b`); the second records a positive exponent.  The elementary counting
estimates in this file apply before interpreting words in a group.
-/

namespace Kourovka.P21_44

abbrev Letter := Bool × Bool
abbrev Word := List Letter

def positive (l : Letter) : ℕ := if l.2 then 1 else 0

def changes (x z : Letter) : ℕ := if x.2 = z.2 then 0 else 1

def descends (x z : Letter) : ℕ := if x.2 = true ∧ z.2 = false then 1 else 0

def variation : Word → ℕ
  | x :: y :: z :: w => changes x z + variation (y :: z :: w)
  | _ => 0

def descents : Word → ℕ
  | x :: y :: z :: w => descends x z + descents (y :: z :: w)
  | _ => 0

def initialSigns : Word → ℕ
  | x :: y :: _ => positive x + positive y
  | [x] => positive x
  | [] => 0

def patternCount : Word → ℕ
  | _x :: y :: z :: t :: u :: w => descends y t + patternCount (y :: z :: t :: u :: w)
  | _ => 0

def isPattern : Word → Bool
  | _ :: y :: _ :: t :: _ :: _ => y.2 && !t.2
  | _ => false

/-- Greedily choose the leftmost eligible interval of length five. -/
def disjointPatterns : Word → ℕ
  | [] => 0
  | x :: w => if isPattern (x :: w) then 1 + disjointPatterns (w.drop 4)
      else disjointPatterns w
termination_by w => w.length
decreasing_by all_goals simp_wf

lemma changes_add_positive (x z : Letter) :
    changes x z + positive x = 2 * descends x z + positive z := by
  rcases x with ⟨x, sx⟩
  rcases z with ⟨z, sz⟩
  cases sx <;> cases sz <;> rfl

lemma variation_add_initial_le (w : Word) :
    variation w + initialSigns w ≤ 2 * descents w + 2 := by
  induction w with
  | nil => simp [variation, initialSigns, descents]
  | cons x w ih =>
    cases w with
    | nil =>
      simp only [variation, initialSigns, descents, Nat.zero_add, Nat.mul_zero]
      unfold positive
      split <;> omega
    | cons y w =>
      cases w with
      | nil =>
        simp only [variation, initialSigns, descents, Nat.zero_add, Nat.mul_zero]
        unfold positive
        split <;> split <;> omega
      | cons z w =>
        change variation (y :: z :: w) + (positive y + positive z) ≤
          2 * descents (y :: z :: w) + 2 at ih
        change changes x z + variation (y :: z :: w) + (positive x + positive y) ≤
          2 * (descends x z + descents (y :: z :: w)) + 2
        have h := changes_add_positive x z
        omega

lemma variation_le (w : Word) : variation w ≤ 2 * descents w + 2 :=
  le_trans (Nat.le_add_right _ _) (variation_add_initial_le w)

lemma descends_le_one (x z : Letter) : descends x z ≤ 1 := by
  unfold descends
  split <;> omega

lemma descents_tail_le (w : Word) : descents w.tail ≤ patternCount w + 1 := by
  induction w with
  | nil => simp [descents, patternCount]
  | cons x w ih =>
    cases w with
    | nil => simp [descents, patternCount]
    | cons y w =>
      cases w with
      | nil => simp [descents, patternCount]
      | cons z w =>
        cases w with
        | nil => simp [descents, patternCount]
        | cons t w =>
          cases w with
          | nil => simpa [descents, patternCount] using descends_le_one y t
          | cons u w =>
            change descents (z :: t :: u :: w) ≤ patternCount (y :: z :: t :: u :: w) + 1 at ih
            change descends y t + descents (z :: t :: u :: w) ≤
              (descends y t + patternCount (y :: z :: t :: u :: w)) + 1
            omega

lemma descents_le_patternCount (w : Word) : descents w ≤ patternCount w + 2 := by
  cases w with
  | nil => simp [descents, patternCount]
  | cons x w =>
    cases w with
    | nil => simp [descents, patternCount]
    | cons y w =>
      cases w with
      | nil => simp [descents, patternCount]
      | cons z w =>
        have h := descents_tail_le (x :: y :: z :: w)
        have hd := descends_le_one x z
        simp only [List.tail_cons, descents] at h ⊢
        omega

lemma patternCount_cons_le (x : Letter) (w : Word) :
    patternCount (x :: w) ≤ 1 + patternCount w := by
  rcases w with _ | ⟨y, w⟩ <;> try simp only [patternCount, Nat.zero_le]
  rcases w with _ | ⟨z, w⟩ <;> try simp only [patternCount, Nat.zero_le]
  rcases w with _ | ⟨t, w⟩ <;> try simp only [patternCount, Nat.zero_le]
  rcases w with _ | ⟨u, w⟩ <;> try simp only [patternCount, Nat.zero_le]
  exact Nat.add_le_add_right (descends_le_one y t) _

lemma patternCount_le_drop (w : Word) (k : ℕ) :
    patternCount w ≤ k + patternCount (w.drop k) := by
  induction k generalizing w with
  | zero => simp
  | succ k ih =>
    cases w with
    | nil => simp [patternCount]
    | cons x w =>
      have h := patternCount_cons_le x w
      have h' := ih w
      simp only [List.drop_succ_cons]
      omega

lemma patternCount_eq_tail_of_not_pattern (x : Letter) (w : Word)
    (h : isPattern (x :: w) = false) : patternCount (x :: w) = patternCount w := by
  rcases w with _ | ⟨y, w⟩ <;> try rfl
  rcases w with _ | ⟨z, w⟩ <;> try rfl
  rcases w with _ | ⟨t, w⟩ <;> try rfl
  rcases w with _ | ⟨u, w⟩ <;> try rfl
  simp only [isPattern, Bool.and_eq_false_iff, Bool.not_eq_false'] at h
  change descends y t + patternCount (y :: z :: t :: u :: w) = patternCount (y :: z :: t :: u :: w)
  have hd : descends y t = 0 := by
    rcases h with h | h <;> simp [descends, h]
  rw [hd, Nat.zero_add]

lemma patternCount_le_five_disjoint (w : Word) :
    patternCount w ≤ 5 * disjointPatterns w := by
  induction n : w.length using Nat.strong_induction_on generalizing w with
  | h n ih =>
    cases w with
    | nil => simp [patternCount, disjointPatterns]
    | cons x w =>
      rw [disjointPatterns]
      split
      · have h := patternCount_le_drop (x :: w) 5
        have h' := ih (w.drop 4).length (by simp at n; simp; omega) _ rfl
        simp only [List.drop_succ_cons] at h
        omega
      · have h' := ih w.length (by simp at n; omega) w rfl
        rw [patternCount_eq_tail_of_not_pattern x w (by simpa using ‹¬ isPattern (x :: w) = true›)]
        exact h'

lemma variation_le_ten_disjoint (w : Word) :
    variation w ≤ 10 * disjointPatterns w + 6 := by
  have h₁ := variation_le w
  have h₂ := descents_le_patternCount w
  have h₃ := patternCount_le_five_disjoint w
  omega

end Kourovka.P21_44
