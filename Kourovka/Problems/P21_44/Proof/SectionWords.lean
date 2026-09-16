import Kourovka.Problems.P21_44.Proof.InverseLimit
import Kourovka.Problems.P21_44.Proof.WordEvaluation

/-! # Explicit section words

Each signed generator contributes its letter to exactly one first-level
section. Subsequent letters are routed by the inverse of the current root
permutation, consistently with `Wreath`.
-/

namespace Kourovka.P21_44

def rootLetter (l : Letter) : A5 :=
  if l.1 then (if l.2 then rootB else rootB⁻¹)
  else (if l.2 then rootA else rootA⁻¹)

def rootWord (w : Word) : A5 := (w.map rootLetter).prod

def activeLetter (l : Letter) : Alphabet := if l.1 then 0 else 3

def letterSection (l : Letter) (i : Alphabet) : Word :=
  if i = activeLetter l then [l] else []

/-- The unreduced words for the five first-level sections. -/
def rawSections : Word → Alphabet → Word
  | [], _ => []
  | l :: w, i => letterSection l i ++ rawSections w ((rootLetter l).val⁻¹ i)

@[simp] theorem rootWord_nil : rootWord [] = 1 := rfl
@[simp] theorem rootWord_cons (l : Letter) (w : Word) :
    rootWord (l :: w) = rootLetter l * rootWord w := rfl
@[simp] theorem rootWord_append (u v : Word) : rootWord (u ++ v) = rootWord u * rootWord v := by
  simp [rootWord]

/-- Concatenation of words concatenates section words after routing the second
factor through the first root action. -/
theorem rawSections_append (u v : Word) (i : Alphabet) :
    rawSections (u ++ v) i = rawSections u i ++ rawSections v ((rootWord u).val⁻¹ i) := by
  induction u generalizing i with
  | nil => rfl
  | cons l u ih =>
    simp only [List.cons_append, rawSections, ih, rootWord_cons, List.append_assoc]
    rfl

theorem sum_letterSection_length (l : Letter) :
    ∑ i : Alphabet, (letterSection l i).length = 1 := by
  simp [letterSection, apply_ite]

theorem sum_rawSections_length (w : Word) :
    ∑ i : Alphabet, (rawSections w i).length = w.length := by
  induction w with
  | nil => simp [rawSections]
  | cons l w ih =>
    simp only [rawSections, List.length_append, Finset.sum_add_distrib]
    rw [sum_letterSection_length]
    have hsum : (∑ i : Alphabet, (rawSections w ((rootLetter l).val⁻¹ i)).length) =
        ∑ i : Alphabet, (rawSections w i).length :=
      Equiv.sum_comp (rootLetter l).val⁻¹ (fun i => (rawSections w i).length)
    rw [hsum, ih, List.length_cons, Nat.add_comm]

@[simp] theorem root_evalLetter (l : Letter) : root (evalLetter a b l) = rootLetter l := by
  rcases l with ⟨f,s⟩
  cases f <;> cases s <;> rfl

@[simp] theorem treeSection_mul (g h : AutTree) (i : Alphabet) :
    treeSection (g*h) i = treeSection g i * treeSection h ((root g).val⁻¹ i) := by
  exact congrArg (fun x : Wreath AutTree => x.left i) (decompose.map_mul g h)

@[simp] theorem treeSection_one (i : Alphabet) : treeSection 1 i = 1 := rfl

theorem treeSection_evalLetter (l : Letter) (i : Alphabet) :
    treeSection (evalLetter a b l) i = evalWord a b (letterSection l i) := by
  change (decompose (evalLetter a b l)).left i = _
  rcases l with ⟨f,s⟩
  cases f <;> cases s <;> fin_cases i <;>
    simp [evalLetter, letterSection, activeLetter, Wreath.inv_left_apply,
      rootA, rootB, Equiv.swap_apply_def]

/-- The explicit section words evaluate to the actual sections of the tree
automorphism represented by the original word. -/
theorem treeSection_evalWord (w : Word) (i : Alphabet) :
    treeSection (evalWord a b w) i = evalWord a b (rawSections w i) := by
  induction w generalizing i with
  | nil => rfl
  | cons l w ih =>
    rw [evalWord_cons, treeSection_mul, treeSection_evalLetter, root_evalLetter, ih]
    exact (evalWord_append a b _ _).symm

end Kourovka.P21_44
