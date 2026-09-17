import Kourovka.Problem2153.Field8

set_option autoImplicit false

namespace Kourovka.Problem2153.WilsonModel.Sparse
open Field8

variable {n : Type*} [Fintype n] [DecidableEq n]

abbrev Row (n : Type*) := List (n × F8)
abbrev Table (n : Type*) := n → Row n

def rowEval : Row n → n → F8
  | [], _ => 0
  | (k, a) :: r, j => (if k = j then a else 0) + rowEval r j

def rowDot : Row n → (n → F8) → F8
  | [], _ => 0
  | (k, a) :: r, b => a * b k + rowDot r b

def eval (a : Table n) : Matrix n n F8 := fun i j => rowEval (a i) j

theorem rowEval_dot (r : Row n) (b : n → F8) :
    (∑ k, rowEval r k * b k) = rowDot r b := by
  induction r with
  | nil => simp [rowEval, rowDot]
  | cons e r ih =>
    rcases e with ⟨k, a⟩
    simp only [rowEval, rowDot, add_mul, Finset.sum_add_distrib, ih]
    congr 1
    simp

/-- Soundness of sparse row evaluation as a matrix multiplication certificate. -/
theorem mul_eq_of_rowDot (a : Table n) (b c : Matrix n n F8)
    (h : ∀ i j, rowDot (a i) (fun k => b k j) = c i j) : eval a * b = c := by
  ext i j
  change (∑ k, rowEval (a i) k * b k j) = c i j
  rw [rowEval_dot]
  exact h i j

/-- A sparse certificate may be attached to any already-defined matrix. -/
theorem mul_eq_of_alignment (a : Matrix n n F8) (sa : Table n)
    (b c : Matrix n n F8) (ha : a = eval sa)
    (h : ∀ i j, rowDot (sa i) (fun k => b k j) = c i j) : a * b = c := by
  rw [ha]
  exact mul_eq_of_rowDot sa b c h

def mulEval (a : Table n) (b : Matrix n n F8) : Matrix n n F8 :=
  fun i j => rowDot (a i) (fun k => b k j)

theorem mul_eq_of_check (a : Table n) (b c : Matrix n n F8)
    (h : mulEval a b = c) : eval a * b = c :=
  mul_eq_of_rowDot a b c (fun i j => congrFun (congrFun h i) j)

theorem mul_eq_of_check_alignment (a : Matrix n n F8) (sa : Table n)
    (b c : Matrix n n F8) (ha : a = eval sa)
    (h : mulEval sa b = c) : a * b = c := by
  rw [ha]
  exact mul_eq_of_check sa b c h

end Kourovka.Problem2153.WilsonModel.Sparse
