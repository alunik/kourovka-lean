import Kourovka.Problem2153.WilsonModel.RootData.Relations.Metadata
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
namespace Kourovka.Problem2153.WilsonModel.RootData.Relations
open Field8 F8
private def inverse_6_target : Mat := 1
private theorem inverse_6_left_s2 : wordMatrix [Atom.root 11 1] = atomMatrix (Atom.root 11 1) := by simp
private def inverse_6_left_m1 : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(1, e1), (5, e1)],
    [(0, e1), (6, e1)],
    [(2, e1), (7, e1)],
    [(8, e1)],
    [(3, e1), (9, e1)],
    [(10, e1)],
    [(4, e1), (11, e1)],
    [(12, e1)],
    [(0, e1), (6, e1), (13, e1)],
    [(5, e1), (14, e1)],
    [(15, e1)],
    [(7, e1), (16, e1)],
    [(17, e1)],
    [(9, e1), (18, e1)],
    [(6, e1), (12, e1), (19, e1)],
    [(11, e1), (20, e1)],
    [(1, e1), (5, e1), (14, e1), (21, e1)],
    [(2, e1), (7, e1), (16, e1), (22, e1)],
    [(3, e1), (9, e1), (18, e1), (23, e1)],
    [(4, e1), (11, e1), (20, e1), (24, e1)],
    [(0, e1), (6, e1), (19, e1), (25, e1)]])
private theorem inverse_6_left_s1 : wordMatrix [Atom.root 6 1, Atom.root 11 1] = inverse_6_left_m1 := by
  rw [wordMatrix_cons, inverse_6_left_s2]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 6 1))
  decide +kernel
private theorem inverse_6_left_s0 : wordMatrix [Atom.root 6 1, Atom.root 6 1, Atom.root 11 1] = inverse_6_target := by
  rw [wordMatrix_cons, inverse_6_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 6 1))
  decide +kernel
private theorem inverse_6_left : wordMatrix [Atom.root 6 1, Atom.root 6 1, Atom.root 11 1] = inverse_6_target := inverse_6_left_s0
private theorem inverse_6_right : wordMatrix [] = inverse_6_target := by decide +kernel
theorem inverse_6 : wordGroup (inverse_lhs 6) = wordGroup (inverse_rhs 6) := by
  apply word_eq_of_matrix_eq
  exact inverse_6_left.trans inverse_6_right.symm

private def inverse_7_target : Mat := 1
private theorem inverse_7_left_s1 : wordMatrix [Atom.root 7 1] = atomMatrix (Atom.root 7 1) := by simp
private theorem inverse_7_left_s0 : wordMatrix [Atom.root 7 1, Atom.root 7 1] = inverse_7_target := by
  rw [wordMatrix_cons, inverse_7_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 7 1))
  decide +kernel
private theorem inverse_7_left : wordMatrix [Atom.root 7 1, Atom.root 7 1] = inverse_7_target := inverse_7_left_s0
private theorem inverse_7_right : wordMatrix [] = inverse_7_target := by decide +kernel
theorem inverse_7 : wordGroup (inverse_lhs 7) = wordGroup (inverse_rhs 7) := by
  apply word_eq_of_matrix_eq
  exact inverse_7_left.trans inverse_7_right.symm

private def inverse_8_target : Mat := 1
private theorem inverse_8_left_s1 : wordMatrix [Atom.root 8 1] = atomMatrix (Atom.root 8 1) := by simp
private theorem inverse_8_left_s0 : wordMatrix [Atom.root 8 1, Atom.root 8 1] = inverse_8_target := by
  rw [wordMatrix_cons, inverse_8_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 8 1))
  decide +kernel
private theorem inverse_8_left : wordMatrix [Atom.root 8 1, Atom.root 8 1] = inverse_8_target := inverse_8_left_s0
private theorem inverse_8_right : wordMatrix [] = inverse_8_target := by decide +kernel
theorem inverse_8 : wordGroup (inverse_lhs 8) = wordGroup (inverse_rhs 8) := by
  apply word_eq_of_matrix_eq
  exact inverse_8_left.trans inverse_8_right.symm

private def inverse_9_target : Mat := 1
private theorem inverse_9_left_s1 : wordMatrix [Atom.root 9 1] = atomMatrix (Atom.root 9 1) := by simp
private theorem inverse_9_left_s0 : wordMatrix [Atom.root 9 1, Atom.root 9 1] = inverse_9_target := by
  rw [wordMatrix_cons, inverse_9_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 9 1))
  decide +kernel
private theorem inverse_9_left : wordMatrix [Atom.root 9 1, Atom.root 9 1] = inverse_9_target := inverse_9_left_s0
private theorem inverse_9_right : wordMatrix [] = inverse_9_target := by decide +kernel
theorem inverse_9 : wordGroup (inverse_lhs 9) = wordGroup (inverse_rhs 9) := by
  apply word_eq_of_matrix_eq
  exact inverse_9_left.trans inverse_9_right.symm

private def inverse_10_target : Mat := 1
private theorem inverse_10_left_s1 : wordMatrix [Atom.root 10 1] = atomMatrix (Atom.root 10 1) := by simp
private theorem inverse_10_left_s0 : wordMatrix [Atom.root 10 1, Atom.root 10 1] = inverse_10_target := by
  rw [wordMatrix_cons, inverse_10_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 10 1))
  decide +kernel
private theorem inverse_10_left : wordMatrix [Atom.root 10 1, Atom.root 10 1] = inverse_10_target := inverse_10_left_s0
private theorem inverse_10_right : wordMatrix [] = inverse_10_target := by decide +kernel
theorem inverse_10 : wordGroup (inverse_lhs 10) = wordGroup (inverse_rhs 10) := by
  apply word_eq_of_matrix_eq
  exact inverse_10_left.trans inverse_10_right.symm

private def inverse_11_target : Mat := 1
private theorem inverse_11_left_s1 : wordMatrix [Atom.root 11 1] = atomMatrix (Atom.root 11 1) := by simp
private theorem inverse_11_left_s0 : wordMatrix [Atom.root 11 1, Atom.root 11 1] = inverse_11_target := by
  rw [wordMatrix_cons, inverse_11_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 11 1))
  decide +kernel
private theorem inverse_11_left : wordMatrix [Atom.root 11 1, Atom.root 11 1] = inverse_11_target := inverse_11_left_s0
private theorem inverse_11_right : wordMatrix [] = inverse_11_target := by decide +kernel
theorem inverse_11 : wordGroup (inverse_lhs 11) = wordGroup (inverse_rhs 11) := by
  apply word_eq_of_matrix_eq
  exact inverse_11_left.trans inverse_11_right.symm

end Kourovka.Problem2153.WilsonModel.RootData.Relations
