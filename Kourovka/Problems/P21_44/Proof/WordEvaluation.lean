import Kourovka.Problems.P21_44.Proof.SignedWords

/-! # Evaluation and alternating representatives

Reduction uses only the two relations `a^3 = b^3 = 1`.  It therefore
provides short alternating representatives in the actual generated group.
-/

namespace Kourovka.P21_44

def flipLetter (x : Letter) : Letter := (x.1, !x.2)

def Alternating : Word → Prop
  | x :: y :: w => x.1 ≠ y.1 ∧ Alternating (y :: w)
  | _ => True

def prependLetter (x : Letter) : Word → Word
  | [] => [x]
  | y :: w => if x.1 = y.1 then
      if x.2 = y.2 then flipLetter x :: w else w
    else x :: y :: w

def normalize : Word → Word
  | [] => []
  | x :: w => prependLetter x (normalize w)

lemma alternating_tail (w : Word) (h : Alternating w) : Alternating w.tail := by
  cases w with
  | nil => trivial
  | cons x w =>
    cases w with
    | nil => trivial
    | cons y w => exact h.2

lemma alternating_prependLetter (x : Letter) (w : Word) (h : Alternating w) :
    Alternating (prependLetter x w) := by
  cases w with
  | nil => trivial
  | cons y w =>
    by_cases hf : x.1 = y.1
    · by_cases hs : x.2 = y.2
      · simp only [prependLetter, hf, hs, ↓reduceIte]
        cases w with
        | nil => trivial
        | cons z w => exact ⟨by simpa only [flipLetter, hf] using h.1, h.2⟩
      · simpa only [prependLetter, hf, hs, ↓reduceIte, List.tail_cons] using alternating_tail (y :: w) h
    · simp only [prependLetter, hf, ↓reduceIte]
      exact ⟨hf, h⟩

lemma alternating_normalize (w : Word) : Alternating (normalize w) := by
  induction w with
  | nil => trivial
  | cons x w ih => exact alternating_prependLetter x _ ih

lemma prependLetter_length_le (x : Letter) (w : Word) :
    (prependLetter x w).length ≤ w.length + 1 := by
  cases w with
  | nil => simp [prependLetter]
  | cons y w =>
    by_cases hf : x.1 = y.1 <;> by_cases hs : x.2 = y.2 <;>
      simp only [prependLetter, hf, hs, ↓reduceIte, List.length_cons] <;> omega

lemma normalize_length_le (w : Word) : (normalize w).length ≤ w.length := by
  induction w with
  | nil => exact le_rfl
  | cons x w ih =>
    have h := prependLetter_length_le x (normalize w)
    change (prependLetter x (normalize w)).length ≤ w.length + 1
    omega

section Evaluation

variable {G : Type*} [Group G]

def evalLetter (a b : G) (l : Letter) : G :=
  if l.1 then (if l.2 then b else b⁻¹) else (if l.2 then a else a⁻¹)

def evalWord (a b : G) (w : Word) : G := (w.map (evalLetter a b)).prod

@[simp] lemma evalWord_nil (a b : G) : evalWord a b [] = 1 := rfl

@[simp] lemma evalWord_cons (a b : G) (x : Letter) (w : Word) :
    evalWord a b (x :: w) = evalLetter a b x * evalWord a b w := rfl

@[simp] lemma evalWord_append (a b : G) (v w : Word) :
    evalWord a b (v ++ w) = evalWord a b v * evalWord a b w := by
  simp [evalWord]

@[simp] lemma evalLetter_flip (a b : G) (x : Letter) :
    evalLetter a b (flipLetter x) = (evalLetter a b x)⁻¹ := by
  rcases x with ⟨f, s⟩
  cases f <;> cases s <;> simp [evalLetter, flipLetter]

@[simp] lemma evalWord_inverse (a b : G) (w : Word) :
    evalWord a b (w.reverse.map flipLetter) = (evalWord a b w)⁻¹ := by
  induction w with
  | nil => simp
  | cons x w ih =>
    simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
      evalWord_append, evalWord_cons, evalWord_nil, evalLetter_flip, mul_one,
      ih, mul_inv_rev]

lemma square_eq_inv_of_cube (g : G) (h : g ^ 3 = 1) : g * g = g⁻¹ := by
  exact eq_inv_of_mul_eq_one_left (by simpa only [pow_succ, pow_zero, one_mul] using h)

lemma inv_square_eq_of_cube (g : G) (h : g ^ 3 = 1) : g⁻¹ * g⁻¹ = g := by
  simpa only [mul_inv_rev, inv_inv] using congrArg Inv.inv (square_eq_inv_of_cube g h)

lemma evalLetter_mul_same (a b : G) (ha : a ^ 3 = 1) (hb : b ^ 3 = 1)
    (x y : Letter) (hf : x.1 = y.1) :
    evalLetter a b x * evalLetter a b y =
      if x.2 = y.2 then evalLetter a b (flipLetter x) else 1 := by
  rcases x with ⟨fx, sx⟩
  rcases y with ⟨fy, sy⟩
  cases fx <;> cases fy <;> cases sx <;> cases sy <;>
    simp_all [evalLetter, flipLetter, square_eq_inv_of_cube]

lemma evalWord_prependLetter (a b : G) (ha : a ^ 3 = 1) (hb : b ^ 3 = 1)
    (x : Letter) (w : Word) :
    evalWord a b (prependLetter x w) = evalLetter a b x * evalWord a b w := by
  cases w with
  | nil => simp [prependLetter]
  | cons y w =>
    by_cases hf : x.1 = y.1
    · have h := evalLetter_mul_same a b ha hb x y hf
      by_cases hs : x.2 = y.2
      · simp only [hs, ↓reduceIte] at h
        simp only [prependLetter, hf, hs, ↓reduceIte, evalWord_cons]
        rw [← h, mul_assoc]
      · simp only [hs, ↓reduceIte] at h
        simp only [prependLetter, hf, hs, ↓reduceIte, evalWord_cons]
        rw [← mul_assoc, h, one_mul]
    · simp [prependLetter, hf]

lemma evalWord_normalize (a b : G) (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) (w : Word) :
    evalWord a b (normalize w) = evalWord a b w := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    rw [normalize, evalWord_prependLetter a b ha hb, ih, evalWord_cons]

lemma exists_evalWord_of_mem_closure (a b : G) {g : G}
    (hg : g ∈ Subgroup.closure ({a, b} : Set G)) :
    ∃ w : Word, evalWord a b w = g := by
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    rcases Set.mem_insert_iff.1 hg with rfl | hg
    · exact ⟨[(false, true)], by simp [evalLetter]⟩
    · have h : g = b := Set.mem_singleton_iff.1 hg
      subst g
      exact ⟨[(true, true)], by simp [evalLetter]⟩
  | one => exact ⟨[], rfl⟩
  | mul g h _ _ hg hh =>
    obtain ⟨u, rfl⟩ := hg
    obtain ⟨v, rfl⟩ := hh
    exact ⟨u ++ v, evalWord_append a b u v⟩
  | inv g _ hg =>
    obtain ⟨w, rfl⟩ := hg
    exact ⟨w.reverse.map flipLetter, evalWord_inverse a b w⟩

lemma evalWord_mem_closure (a b : G) (w : Word) :
    evalWord a b w ∈ Subgroup.closure ({a, b} : Set G) := by
  have ha : a ∈ Subgroup.closure ({a, b} : Set G) := Subgroup.subset_closure (by simp)
  have hb : b ∈ Subgroup.closure ({a, b} : Set G) := Subgroup.subset_closure (by simp)
  induction w with
  | nil => exact Subgroup.one_mem _
  | cons x w ih =>
    apply Subgroup.mul_mem _ _ ih
    rcases x with ⟨f, s⟩
    cases f <;> cases s <;> simp only [evalLetter, Bool.false_eq_true, ↓reduceIte]
    · exact Subgroup.inv_mem _ ha
    · exact ha
    · exact Subgroup.inv_mem _ hb
    · exact hb

end Evaluation
end Kourovka.P21_44
