import Kourovka.Problem2153.WilsonModel.RootData.Relations.Metadata
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
namespace Kourovka.Problem2153.WilsonModel.RootData.Relations
open Field8 F8
private def commutator_6_target : Mat := Sparse.eval (![[(0, e1)],
    [(0, e1), (1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(0, e1), (3, e1), (5, e1)],
    [(4, e1), (6, e1)],
    [(4, e1), (7, e1)],
    [(0, e1), (2, e1), (4, e1), (6, e1), (7, e1), (8, e1)],
    [(9, e1)],
    [(3, e1), (9, e1), (10, e1)],
    [(11, e1)],
    [(4, e1), (11, e1), (12, e1)],
    [(4, e1), (13, e1)],
    [(3, e1), (4, e1), (6, e1), (11, e1), (13, e1), (14, e1)],
    [(15, e1)],
    [(4, e1), (15, e1), (16, e1)],
    [(17, e1)],
    [(17, e1), (18, e1)],
    [(11, e1), (17, e1), (19, e1)],
    [(20, e1)],
    [(4, e1), (9, e1), (11, e1), (12, e1), (13, e1), (17, e1), (18, e1), (19, e1), (21, e1)],
    [(11, e1), (15, e1), (20, e1), (22, e1)],
    [(17, e1), (23, e1)],
    [(24, e1)],
    [(17, e1), (20, e1), (24, e1), (25, e1)]])
private theorem commutator_6_left_s1 : wordMatrix [Atom.root 7 1] = atomMatrix (Atom.root 7 1) := by simp
private theorem commutator_6_left_s0 : wordMatrix [Atom.root 0 1, Atom.root 7 1] = commutator_6_target := by
  rw [wordMatrix_cons, commutator_6_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 0 1))
  decide +kernel
private theorem commutator_6_left : wordMatrix [Atom.root 0 1, Atom.root 7 1] = commutator_6_target := commutator_6_left_s0
private theorem commutator_6_right_s1 : wordMatrix [Atom.root 0 1] = atomMatrix (Atom.root 0 1) := by simp
private theorem commutator_6_right_s0 : wordMatrix [Atom.root 7 1, Atom.root 0 1] = commutator_6_target := by
  rw [wordMatrix_cons, commutator_6_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 7 1))
  decide +kernel
private theorem commutator_6_right : wordMatrix [Atom.root 7 1, Atom.root 0 1] = commutator_6_target := commutator_6_right_s0
theorem commutator_6 : wordGroup (commutator_lhs 6) = wordGroup (commutator_rhs 6) := by
  apply word_eq_of_matrix_eq
  exact commutator_6_left.trans commutator_6_right.symm

private def commutator_7_target : Mat := Sparse.eval (![[(0, e1)],
    [(0, e1), (1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(3, e1), (5, e1)],
    [(4, e1), (6, e1)],
    [(0, e1), (4, e1), (7, e1)],
    [(0, e1), (1, e1), (4, e1), (6, e1), (7, e1), (8, e1)],
    [(9, e1)],
    [(0, e1), (9, e1), (10, e1)],
    [(11, e1)],
    [(3, e1), (11, e1), (12, e1)],
    [(13, e1)],
    [(2, e1), (11, e1), (13, e1), (14, e1)],
    [(4, e1), (15, e1)],
    [(4, e1), (6, e1), (15, e1), (16, e1)],
    [(17, e1)],
    [(4, e1), (17, e1), (18, e1)],
    [(9, e1), (17, e1), (19, e1)],
    [(20, e1)],
    [(0, e1), (4, e1), (7, e1), (9, e1), (10, e1), (17, e1), (18, e1), (19, e1), (21, e1)],
    [(3, e1), (13, e1), (20, e1), (22, e1)],
    [(11, e1), (23, e1)],
    [(17, e1), (24, e1)],
    [(4, e1), (15, e1), (17, e1), (18, e1), (24, e1), (25, e1)]])
private theorem commutator_7_left_s1 : wordMatrix [Atom.root 8 1] = atomMatrix (Atom.root 8 1) := by simp
private theorem commutator_7_left_s0 : wordMatrix [Atom.root 0 1, Atom.root 8 1] = commutator_7_target := by
  rw [wordMatrix_cons, commutator_7_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 0 1))
  decide +kernel
private theorem commutator_7_left : wordMatrix [Atom.root 0 1, Atom.root 8 1] = commutator_7_target := commutator_7_left_s0
private theorem commutator_7_right_s1 : wordMatrix [Atom.root 0 1] = atomMatrix (Atom.root 0 1) := by simp
private theorem commutator_7_right_s0 : wordMatrix [Atom.root 8 1, Atom.root 0 1] = commutator_7_target := by
  rw [wordMatrix_cons, commutator_7_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 8 1))
  decide +kernel
private theorem commutator_7_right : wordMatrix [Atom.root 8 1, Atom.root 0 1] = commutator_7_target := commutator_7_right_s0
theorem commutator_7 : wordGroup (commutator_lhs 7) = wordGroup (commutator_rhs 7) := by
  apply word_eq_of_matrix_eq
  exact commutator_7_left.trans commutator_7_right.symm

private def commutator_8_target : Mat := Sparse.eval (![[(0, e1)],
    [(0, e1), (1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(3, e1), (5, e1)],
    [(4, e1), (6, e1)],
    [(4, e1), (7, e1)],
    [(4, e1), (6, e1), (7, e1), (8, e1)],
    [(0, e1), (9, e1)],
    [(0, e1), (1, e1), (9, e1), (10, e1)],
    [(11, e1)],
    [(2, e1), (11, e1), (12, e1)],
    [(13, e1)],
    [(11, e1), (13, e1), (14, e1)],
    [(0, e1), (15, e1)],
    [(0, e1), (1, e1), (15, e1), (16, e1)],
    [(4, e1), (17, e1)],
    [(4, e1), (6, e1), (17, e1), (18, e1)],
    [(4, e1), (7, e1), (17, e1), (19, e1)],
    [(3, e1), (20, e1)],
    [(4, e1), (6, e1), (7, e1), (8, e1), (17, e1), (18, e1), (19, e1), (21, e1)],
    [(3, e1), (5, e1), (20, e1), (22, e1)],
    [(2, e1), (13, e1), (23, e1)],
    [(0, e1), (9, e1), (15, e1), (24, e1)],
    [(0, e1), (1, e1), (9, e1), (10, e1), (15, e1), (16, e1), (24, e1), (25, e1)]])
private theorem commutator_8_left_s1 : wordMatrix [Atom.root 9 1] = atomMatrix (Atom.root 9 1) := by simp
private theorem commutator_8_left_s0 : wordMatrix [Atom.root 0 1, Atom.root 9 1] = commutator_8_target := by
  rw [wordMatrix_cons, commutator_8_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 0 1))
  decide +kernel
private theorem commutator_8_left : wordMatrix [Atom.root 0 1, Atom.root 9 1] = commutator_8_target := commutator_8_left_s0
private theorem commutator_8_right_s1 : wordMatrix [Atom.root 0 1] = atomMatrix (Atom.root 0 1) := by simp
private theorem commutator_8_right_s0 : wordMatrix [Atom.root 9 1, Atom.root 0 1] = commutator_8_target := by
  rw [wordMatrix_cons, commutator_8_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 9 1))
  decide +kernel
private theorem commutator_8_right : wordMatrix [Atom.root 9 1, Atom.root 0 1] = commutator_8_target := commutator_8_right_s0
theorem commutator_8 : wordGroup (commutator_lhs 8) = wordGroup (commutator_rhs 8) := by
  apply word_eq_of_matrix_eq
  exact commutator_8_left.trans commutator_8_right.symm

private def commutator_9_target : Mat := Sparse.eval (![[(0, e1)],
    [(0, e1), (1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(3, e1), (5, e1)],
    [(4, e1), (6, e1)],
    [(4, e1), (7, e1)],
    [(4, e1), (6, e1), (7, e1), (8, e1)],
    [(9, e1)],
    [(9, e1), (10, e1)],
    [(0, e1), (11, e1)],
    [(0, e1), (1, e1), (11, e1), (12, e1)],
    [(1, e1), (13, e1)],
    [(0, e1), (1, e1), (11, e1), (13, e1), (14, e1)],
    [(2, e1), (15, e1)],
    [(2, e1), (15, e1), (16, e1)],
    [(0, e1), (3, e1), (17, e1)],
    [(0, e1), (1, e1), (3, e1), (17, e1), (18, e1)],
    [(0, e1), (3, e1), (5, e1), (17, e1), (19, e1)],
    [(2, e1), (6, e1), (20, e1)],
    [(0, e1), (1, e1), (3, e1), (5, e1), (17, e1), (18, e1), (19, e1), (21, e1)],
    [(2, e1), (6, e1), (8, e1), (20, e1), (22, e1)],
    [(5, e1), (10, e1), (23, e1)],
    [(1, e1), (7, e1), (12, e1), (13, e1), (24, e1)],
    [(1, e1), (7, e1), (8, e1), (12, e1), (13, e1), (14, e1), (24, e1), (25, e1)]])
private theorem commutator_9_left_s1 : wordMatrix [Atom.root 10 1] = atomMatrix (Atom.root 10 1) := by simp
private theorem commutator_9_left_s0 : wordMatrix [Atom.root 0 1, Atom.root 10 1] = commutator_9_target := by
  rw [wordMatrix_cons, commutator_9_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 0 1))
  decide +kernel
private theorem commutator_9_left : wordMatrix [Atom.root 0 1, Atom.root 10 1] = commutator_9_target := commutator_9_left_s0
private theorem commutator_9_right_s2 : wordMatrix [Atom.root 11 1] = atomMatrix (Atom.root 11 1) := by simp
private def commutator_9_right_m1 : Mat := Sparse.eval (![[(0, e1)],
    [(0, e1), (1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(3, e1), (5, e1)],
    [(4, e1), (6, e1)],
    [(4, e1), (7, e1)],
    [(4, e1), (6, e1), (7, e1), (8, e1)],
    [(9, e1)],
    [(9, e1), (10, e1)],
    [(11, e1)],
    [(11, e1), (12, e1)],
    [(0, e1), (13, e1)],
    [(0, e1), (1, e1), (11, e1), (13, e1), (14, e1)],
    [(15, e1)],
    [(2, e1), (15, e1), (16, e1)],
    [(17, e1)],
    [(3, e1), (17, e1), (18, e1)],
    [(0, e1), (17, e1), (19, e1)],
    [(4, e1), (20, e1)],
    [(0, e1), (1, e1), (3, e1), (5, e1), (17, e1), (18, e1), (19, e1), (21, e1)],
    [(2, e1), (4, e1), (7, e1), (20, e1), (22, e1)],
    [(3, e1), (9, e1), (23, e1)],
    [(4, e1), (11, e1), (24, e1)],
    [(0, e1), (4, e1), (6, e1), (11, e1), (12, e1), (24, e1), (25, e1)]])
private theorem commutator_9_right_s1 : wordMatrix [Atom.root 0 1, Atom.root 11 1] = commutator_9_right_m1 := by
  rw [wordMatrix_cons, commutator_9_right_s2]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 0 1))
  decide +kernel
private theorem commutator_9_right_s0 : wordMatrix [Atom.root 10 1, Atom.root 0 1, Atom.root 11 1] = commutator_9_target := by
  rw [wordMatrix_cons, commutator_9_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 10 1))
  decide +kernel
private theorem commutator_9_right : wordMatrix [Atom.root 10 1, Atom.root 0 1, Atom.root 11 1] = commutator_9_target := commutator_9_right_s0
theorem commutator_9 : wordGroup (commutator_lhs 9) = wordGroup (commutator_rhs 9) := by
  apply word_eq_of_matrix_eq
  exact commutator_9_left.trans commutator_9_right.symm

private def commutator_10_target : Mat := Sparse.eval (![[(0, e1)],
    [(0, e1), (1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(3, e1), (5, e1)],
    [(4, e1), (6, e1)],
    [(4, e1), (7, e1)],
    [(4, e1), (6, e1), (7, e1), (8, e1)],
    [(9, e1)],
    [(9, e1), (10, e1)],
    [(11, e1)],
    [(11, e1), (12, e1)],
    [(0, e1), (13, e1)],
    [(0, e1), (1, e1), (11, e1), (13, e1), (14, e1)],
    [(15, e1)],
    [(2, e1), (15, e1), (16, e1)],
    [(17, e1)],
    [(3, e1), (17, e1), (18, e1)],
    [(0, e1), (17, e1), (19, e1)],
    [(4, e1), (20, e1)],
    [(0, e1), (1, e1), (3, e1), (5, e1), (17, e1), (18, e1), (19, e1), (21, e1)],
    [(2, e1), (4, e1), (7, e1), (20, e1), (22, e1)],
    [(3, e1), (9, e1), (23, e1)],
    [(4, e1), (11, e1), (24, e1)],
    [(0, e1), (4, e1), (6, e1), (11, e1), (12, e1), (24, e1), (25, e1)]])
private theorem commutator_10_left_s1 : wordMatrix [Atom.root 11 1] = atomMatrix (Atom.root 11 1) := by simp
private theorem commutator_10_left_s0 : wordMatrix [Atom.root 0 1, Atom.root 11 1] = commutator_10_target := by
  rw [wordMatrix_cons, commutator_10_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 0 1))
  decide +kernel
private theorem commutator_10_left : wordMatrix [Atom.root 0 1, Atom.root 11 1] = commutator_10_target := commutator_10_left_s0
private theorem commutator_10_right_s1 : wordMatrix [Atom.root 0 1] = atomMatrix (Atom.root 0 1) := by simp
private theorem commutator_10_right_s0 : wordMatrix [Atom.root 11 1, Atom.root 0 1] = commutator_10_target := by
  rw [wordMatrix_cons, commutator_10_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 11 1))
  decide +kernel
private theorem commutator_10_right : wordMatrix [Atom.root 11 1, Atom.root 0 1] = commutator_10_target := commutator_10_right_s0
theorem commutator_10 : wordGroup (commutator_lhs 10) = wordGroup (commutator_rhs 10) := by
  apply word_eq_of_matrix_eq
  exact commutator_10_left.trans commutator_10_right.symm

private def commutator_11_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(0, e1), (1, e1), (2, e1)],
    [(0, e1), (1, e1), (2, e1), (3, e1)],
    [(1, e1), (3, e1), (4, e1)],
    [(0, e1), (2, e1), (5, e1)],
    [(3, e1), (6, e1)],
    [(0, e1), (2, e1), (5, e1), (7, e1)],
    [(0, e1), (5, e1), (8, e1)],
    [(0, e1), (2, e1), (4, e1), (5, e1), (7, e1), (9, e1)],
    [(0, e1), (3, e1), (5, e1), (6, e1), (8, e1), (10, e1)],
    [(0, e1), (2, e1), (4, e1), (5, e1), (9, e1), (11, e1)],
    [(9, e1), (12, e1)],
    [(3, e1), (6, e1), (9, e1), (10, e1), (13, e1)],
    [(3, e1), (10, e1), (14, e1)],
    [(0, e1), (3, e1), (5, e1), (6, e1), (8, e1), (9, e1), (10, e1), (11, e1), (12, e1), (15, e1)],
    [(3, e1), (4, e1), (9, e1), (10, e1), (12, e1), (13, e1), (14, e1), (16, e1)],
    [(0, e1), (5, e1), (8, e1), (9, e1), (11, e1), (12, e1), (15, e1), (17, e1)],
    [(3, e1), (4, e1), (9, e1), (10, e1), (12, e1), (13, e1), (14, e1), (16, e1), (18, e1)],
    [(11, e1), (15, e1), (19, e1)],
    [(3, e1), (10, e1), (14, e1), (17, e1), (18, e1), (20, e1)],
    [(4, e1), (12, e1), (13, e1), (16, e1), (21, e1)],
    [(4, e1), (11, e1), (12, e1), (13, e1), (16, e1), (19, e1), (21, e1), (22, e1)],
    [(4, e1), (11, e1), (12, e1), (13, e1), (16, e1), (17, e1), (19, e1), (20, e1), (21, e1), (22, e1), (23, e1)],
    [(4, e1), (12, e1), (13, e1), (16, e1), (17, e1), (20, e1), (21, e1), (23, e1), (24, e1)],
    [(17, e1), (23, e1), (25, e1)]])
private theorem commutator_11_left_s1 : wordMatrix [Atom.root 2 1] = atomMatrix (Atom.root 2 1) := by simp
private theorem commutator_11_left_s0 : wordMatrix [Atom.root 1 1, Atom.root 2 1] = commutator_11_target := by
  rw [wordMatrix_cons, commutator_11_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 1 1))
  decide +kernel
private theorem commutator_11_left : wordMatrix [Atom.root 1 1, Atom.root 2 1] = commutator_11_target := commutator_11_left_s0
private theorem commutator_11_right_s6 : wordMatrix [Atom.root 11 1] = atomMatrix (Atom.root 11 1) := by simp
private def commutator_11_right_m5 : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(5, e1)],
    [(6, e1)],
    [(0, e1), (7, e1)],
    [(1, e1), (8, e1)],
    [(9, e1)],
    [(0, e1), (10, e1)],
    [(11, e1)],
    [(3, e1), (12, e1)],
    [(0, e1), (13, e1)],
    [(1, e1), (2, e1), (14, e1)],
    [(4, e1), (15, e1)],
    [(2, e1), (6, e1), (16, e1)],
    [(17, e1)],
    [(3, e1), (4, e1), (18, e1)],
    [(0, e1), (9, e1), (19, e1)],
    [(4, e1), (20, e1)],
    [(0, e1), (1, e1), (5, e1), (7, e1), (10, e1), (21, e1)],
    [(0, e1), (2, e1), (3, e1), (7, e1), (13, e1), (22, e1)],
    [(3, e1), (9, e1), (11, e1), (23, e1)],
    [(4, e1), (11, e1), (17, e1), (24, e1)],
    [(0, e1), (3, e1), (4, e1), (6, e1), (12, e1), (15, e1), (18, e1), (25, e1)]])
private theorem commutator_11_right_s5 : wordMatrix [Atom.root 8 1, Atom.root 11 1] = commutator_11_right_m5 := by
  rw [wordMatrix_cons, commutator_11_right_s6]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 8 1))
  decide +kernel
private def commutator_11_right_m4 : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(1, e1), (5, e1)],
    [(0, e1), (6, e1)],
    [(0, e1), (2, e1), (7, e1)],
    [(1, e1), (8, e1)],
    [(3, e1), (9, e1)],
    [(0, e1), (10, e1)],
    [(4, e1), (11, e1)],
    [(3, e1), (12, e1)],
    [(0, e1), (6, e1), (13, e1)],
    [(2, e1), (5, e1), (14, e1)],
    [(4, e1), (15, e1)],
    [(0, e1), (6, e1), (7, e1), (16, e1)],
    [(17, e1)],
    [(4, e1), (9, e1), (18, e1)],
    [(3, e1), (6, e1), (9, e1), (12, e1), (19, e1)],
    [(11, e1), (20, e1)],
    [(0, e1), (1, e1), (2, e1), (5, e1), (7, e1), (10, e1), (14, e1), (21, e1)],
    [(0, e1), (2, e1), (3, e1), (6, e1), (7, e1), (13, e1), (16, e1), (22, e1)],
    [(3, e1), (4, e1), (9, e1), (11, e1), (18, e1), (23, e1)],
    [(4, e1), (11, e1), (17, e1), (20, e1), (24, e1)],
    [(0, e1), (4, e1), (6, e1), (9, e1), (15, e1), (18, e1), (19, e1), (25, e1)]])
private theorem commutator_11_right_s4 : wordMatrix [Atom.root 6 1, Atom.root 8 1, Atom.root 11 1] = commutator_11_right_m4 := by
  rw [wordMatrix_cons, commutator_11_right_s5]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 6 1))
  decide +kernel
private def commutator_11_right_m3 : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(0, e1), (4, e1)],
    [(1, e1), (5, e1)],
    [(0, e1), (1, e1), (6, e1)],
    [(0, e1), (2, e1), (7, e1)],
    [(1, e1), (8, e1)],
    [(1, e1), (3, e1), (9, e1)],
    [(0, e1), (10, e1)],
    [(2, e1), (4, e1), (11, e1)],
    [(1, e1), (3, e1), (5, e1), (12, e1)],
    [(0, e1), (6, e1), (13, e1)],
    [(2, e1), (5, e1), (14, e1)],
    [(0, e1), (2, e1), (4, e1), (7, e1), (15, e1)],
    [(0, e1), (1, e1), (6, e1), (7, e1), (8, e1), (16, e1)],
    [(0, e1), (1, e1), (3, e1), (6, e1), (9, e1), (17, e1)],
    [(0, e1), (4, e1), (9, e1), (10, e1), (18, e1)],
    [(1, e1), (3, e1), (6, e1), (8, e1), (9, e1), (12, e1), (19, e1)],
    [(0, e1), (1, e1), (5, e1), (6, e1), (11, e1), (13, e1), (20, e1)],
    [(0, e1), (1, e1), (2, e1), (5, e1), (7, e1), (10, e1), (14, e1), (21, e1)],
    [(0, e1), (2, e1), (3, e1), (6, e1), (7, e1), (13, e1), (16, e1), (22, e1)],
    [(2, e1), (3, e1), (4, e1), (5, e1), (9, e1), (11, e1), (14, e1), (18, e1), (23, e1)],
    [(0, e1), (1, e1), (3, e1), (4, e1), (7, e1), (8, e1), (9, e1), (11, e1), (12, e1), (16, e1), (17, e1), (19, e1), (20, e1), (24, e1)],
    [(1, e1), (2, e1), (4, e1), (5, e1), (6, e1), (7, e1), (9, e1), (10, e1), (14, e1), (15, e1), (18, e1), (19, e1), (21, e1), (25, e1)]])
private theorem commutator_11_right_s3 : wordMatrix [Atom.root 5 1, Atom.root 6 1, Atom.root 8 1, Atom.root 11 1] = commutator_11_right_m3 := by
  rw [wordMatrix_cons, commutator_11_right_s4]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 5 1))
  decide +kernel
private def commutator_11_right_m2 : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(0, e1), (3, e1)],
    [(0, e1), (4, e1)],
    [(1, e1), (5, e1)],
    [(0, e1), (1, e1), (2, e1), (6, e1)],
    [(0, e1), (1, e1), (2, e1), (7, e1)],
    [(1, e1), (8, e1)],
    [(1, e1), (3, e1), (9, e1)],
    [(0, e1), (1, e1), (5, e1), (10, e1)],
    [(0, e1), (2, e1), (3, e1), (4, e1), (11, e1)],
    [(0, e1), (1, e1), (2, e1), (3, e1), (5, e1), (7, e1), (12, e1)],
    [(2, e1), (6, e1), (7, e1), (13, e1)],
    [(1, e1), (2, e1), (5, e1), (8, e1), (14, e1)],
    [(1, e1), (4, e1), (6, e1), (7, e1), (15, e1)],
    [(0, e1), (1, e1), (6, e1), (7, e1), (8, e1), (16, e1)],
    [(1, e1), (2, e1), (3, e1), (4, e1), (6, e1), (9, e1), (11, e1), (17, e1)],
    [(0, e1), (2, e1), (3, e1), (4, e1), (5, e1), (6, e1), (7, e1), (9, e1), (10, e1), (12, e1), (13, e1), (18, e1)],
    [(0, e1), (3, e1), (5, e1), (6, e1), (8, e1), (9, e1), (10, e1), (12, e1), (19, e1)],
    [(1, e1), (4, e1), (5, e1), (6, e1), (7, e1), (11, e1), (13, e1), (15, e1), (20, e1)],
    [(0, e1), (1, e1), (2, e1), (5, e1), (7, e1), (10, e1), (14, e1), (21, e1)],
    [(0, e1), (1, e1), (3, e1), (5, e1), (6, e1), (7, e1), (8, e1), (13, e1), (14, e1), (16, e1), (22, e1)],
    [(2, e1), (4, e1), (6, e1), (8, e1), (11, e1), (12, e1), (14, e1), (18, e1), (19, e1), (23, e1)],
    [(0, e1), (1, e1), (5, e1), (6, e1), (7, e1), (8, e1), (10, e1), (11, e1), (13, e1), (16, e1), (17, e1), (18, e1), (19, e1), (20, e1), (24, e1)],
    [(0, e1), (3, e1), (4, e1), (5, e1), (8, e1), (9, e1), (10, e1), (13, e1), (14, e1), (15, e1), (16, e1), (18, e1), (19, e1), (21, e1), (22, e1), (25, e1)]])
private theorem commutator_11_right_s2 : wordMatrix [Atom.root 4 1, Atom.root 5 1, Atom.root 6 1, Atom.root 8 1, Atom.root 11 1] = commutator_11_right_m2 := by
  rw [wordMatrix_cons, commutator_11_right_s3]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 4 1))
  decide +kernel
private def commutator_11_right_m1 : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(1, e1), (2, e1)],
    [(0, e1), (1, e1), (2, e1), (3, e1)],
    [(1, e1), (3, e1), (4, e1)],
    [(1, e1), (5, e1)],
    [(0, e1), (1, e1), (2, e1), (6, e1)],
    [(0, e1), (2, e1), (5, e1), (7, e1)],
    [(1, e1), (8, e1)],
    [(0, e1), (1, e1), (2, e1), (3, e1), (5, e1), (7, e1), (9, e1)],
    [(0, e1), (5, e1), (8, e1), (10, e1)],
    [(0, e1), (2, e1), (4, e1), (5, e1), (9, e1), (11, e1)],
    [(0, e1), (1, e1), (2, e1), (3, e1), (5, e1), (7, e1), (12, e1)],
    [(0, e1), (1, e1), (2, e1), (5, e1), (6, e1), (7, e1), (10, e1), (13, e1)],
    [(1, e1), (2, e1), (5, e1), (8, e1), (14, e1)],
    [(2, e1), (3, e1), (4, e1), (6, e1), (8, e1), (10, e1), (12, e1), (15, e1)],
    [(0, e1), (2, e1), (5, e1), (6, e1), (7, e1), (14, e1), (16, e1)],
    [(0, e1), (5, e1), (8, e1), (9, e1), (11, e1), (12, e1), (15, e1), (17, e1)],
    [(3, e1), (4, e1), (9, e1), (10, e1), (12, e1), (13, e1), (14, e1), (16, e1), (18, e1)],
    [(0, e1), (3, e1), (5, e1), (6, e1), (8, e1), (9, e1), (10, e1), (12, e1), (19, e1)],
    [(0, e1), (3, e1), (5, e1), (8, e1), (9, e1), (10, e1), (11, e1), (12, e1), (14, e1), (15, e1), (18, e1), (20, e1)],
    [(0, e1), (1, e1), (2, e1), (5, e1), (7, e1), (10, e1), (14, e1), (21, e1)],
    [(2, e1), (3, e1), (6, e1), (8, e1), (10, e1), (13, e1), (16, e1), (21, e1), (22, e1)],
    [(3, e1), (4, e1), (10, e1), (11, e1), (12, e1), (13, e1), (14, e1), (16, e1), (18, e1), (19, e1), (21, e1), (22, e1), (23, e1)],
    [(4, e1), (12, e1), (13, e1), (16, e1), (17, e1), (20, e1), (21, e1), (23, e1), (24, e1)],
    [(0, e1), (3, e1), (4, e1), (5, e1), (8, e1), (9, e1), (10, e1), (13, e1), (14, e1), (15, e1), (16, e1), (18, e1), (19, e1), (21, e1), (22, e1), (25, e1)]])
private theorem commutator_11_right_s1 : wordMatrix [Atom.root 1 1, Atom.root 4 1, Atom.root 5 1, Atom.root 6 1, Atom.root 8 1, Atom.root 11 1] = commutator_11_right_m1 := by
  rw [wordMatrix_cons, commutator_11_right_s2]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 1 1))
  decide +kernel
private theorem commutator_11_right_s0 : wordMatrix [Atom.root 2 1, Atom.root 1 1, Atom.root 4 1, Atom.root 5 1, Atom.root 6 1, Atom.root 8 1, Atom.root 11 1] = commutator_11_target := by
  rw [wordMatrix_cons, commutator_11_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 2 1))
  decide +kernel
private theorem commutator_11_right : wordMatrix [Atom.root 2 1, Atom.root 1 1, Atom.root 4 1, Atom.root 5 1, Atom.root 6 1, Atom.root 8 1, Atom.root 11 1] = commutator_11_target := commutator_11_right_s0
theorem commutator_11 : wordGroup (commutator_lhs 11) = wordGroup (commutator_rhs 11) := by
  apply word_eq_of_matrix_eq
  exact commutator_11_left.trans commutator_11_right.symm

end Kourovka.Problem2153.WilsonModel.RootData.Relations
