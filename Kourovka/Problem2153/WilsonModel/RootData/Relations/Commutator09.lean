import Kourovka.Problem2153.WilsonModel.RootData.Relations.Metadata
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
namespace Kourovka.Problem2153.WilsonModel.RootData.Relations
open Field8 F8
private def commutator_54_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(0, e1), (3, e1)],
    [(4, e1)],
    [(5, e1)],
    [(2, e1), (6, e1)],
    [(1, e1), (7, e1)],
    [(8, e1)],
    [(0, e1), (9, e1)],
    [(1, e1), (5, e1), (10, e1)],
    [(0, e1), (3, e1), (11, e1)],
    [(2, e1), (7, e1), (12, e1)],
    [(7, e1), (13, e1)],
    [(8, e1), (14, e1)],
    [(0, e1), (2, e1), (6, e1), (15, e1)],
    [(1, e1), (16, e1)],
    [(0, e1), (4, e1), (11, e1), (17, e1)],
    [(1, e1), (2, e1), (6, e1), (7, e1), (12, e1), (13, e1), (18, e1)],
    [(1, e1), (5, e1), (7, e1), (10, e1), (19, e1)],
    [(0, e1), (2, e1), (3, e1), (15, e1), (20, e1)],
    [(8, e1), (21, e1)],
    [(5, e1), (8, e1), (14, e1), (22, e1)],
    [(2, e1), (5, e1), (7, e1), (13, e1), (19, e1), (23, e1)],
    [(0, e1), (1, e1), (2, e1), (6, e1), (9, e1), (12, e1), (13, e1), (15, e1), (18, e1), (24, e1)],
    [(1, e1), (5, e1), (8, e1), (10, e1), (16, e1), (22, e1), (25, e1)]])
private theorem commutator_54_left_s1 : wordMatrix [Atom.root 9 1] = atomMatrix (Atom.root 9 1) := by simp
private theorem commutator_54_left_s0 : wordMatrix [Atom.root 4 1, Atom.root 9 1] = commutator_54_target := by
  rw [wordMatrix_cons, commutator_54_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 4 1))
  decide +kernel
private theorem commutator_54_left : wordMatrix [Atom.root 4 1, Atom.root 9 1] = commutator_54_target := commutator_54_left_s0
private theorem commutator_54_right_s1 : wordMatrix [Atom.root 4 1] = atomMatrix (Atom.root 4 1) := by simp
private theorem commutator_54_right_s0 : wordMatrix [Atom.root 9 1, Atom.root 4 1] = commutator_54_target := by
  rw [wordMatrix_cons, commutator_54_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 9 1))
  decide +kernel
private theorem commutator_54_right : wordMatrix [Atom.root 9 1, Atom.root 4 1] = commutator_54_target := commutator_54_right_s0
theorem commutator_54 : wordGroup (commutator_lhs 54) = wordGroup (commutator_rhs 54) := by
  apply word_eq_of_matrix_eq
  exact commutator_54_left.trans commutator_54_right.symm

private def commutator_55_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(0, e1), (3, e1)],
    [(4, e1)],
    [(5, e1)],
    [(2, e1), (6, e1)],
    [(1, e1), (7, e1)],
    [(8, e1)],
    [(9, e1)],
    [(5, e1), (10, e1)],
    [(3, e1), (11, e1)],
    [(1, e1), (7, e1), (12, e1)],
    [(1, e1), (7, e1), (13, e1)],
    [(8, e1), (14, e1)],
    [(6, e1), (15, e1)],
    [(16, e1)],
    [(0, e1), (3, e1), (11, e1), (17, e1)],
    [(7, e1), (12, e1), (13, e1), (18, e1)],
    [(10, e1), (19, e1)],
    [(2, e1), (6, e1), (15, e1), (20, e1)],
    [(21, e1)],
    [(14, e1), (22, e1)],
    [(5, e1), (10, e1), (19, e1), (23, e1)],
    [(1, e1), (7, e1), (18, e1), (24, e1)],
    [(8, e1), (14, e1), (22, e1), (25, e1)]])
private theorem commutator_55_left_s1 : wordMatrix [Atom.root 10 1] = atomMatrix (Atom.root 10 1) := by simp
private theorem commutator_55_left_s0 : wordMatrix [Atom.root 4 1, Atom.root 10 1] = commutator_55_target := by
  rw [wordMatrix_cons, commutator_55_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 4 1))
  decide +kernel
private theorem commutator_55_left : wordMatrix [Atom.root 4 1, Atom.root 10 1] = commutator_55_target := commutator_55_left_s0
private theorem commutator_55_right_s1 : wordMatrix [Atom.root 4 1] = atomMatrix (Atom.root 4 1) := by simp
private theorem commutator_55_right_s0 : wordMatrix [Atom.root 10 1, Atom.root 4 1] = commutator_55_target := by
  rw [wordMatrix_cons, commutator_55_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 10 1))
  decide +kernel
private theorem commutator_55_right : wordMatrix [Atom.root 10 1, Atom.root 4 1] = commutator_55_target := commutator_55_right_s0
theorem commutator_55 : wordGroup (commutator_lhs 55) = wordGroup (commutator_rhs 55) := by
  apply word_eq_of_matrix_eq
  exact commutator_55_left.trans commutator_55_right.symm

private def commutator_56_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(0, e1), (3, e1)],
    [(4, e1)],
    [(5, e1)],
    [(2, e1), (6, e1)],
    [(1, e1), (7, e1)],
    [(8, e1)],
    [(9, e1)],
    [(5, e1), (10, e1)],
    [(0, e3), (3, e1), (11, e1)],
    [(1, e2), (7, e1), (12, e1)],
    [(1, e2), (7, e1), (13, e1)],
    [(8, e1), (14, e1)],
    [(2, e3), (6, e1), (15, e1)],
    [(16, e1)],
    [(0, e5), (3, e2), (11, e1), (17, e1)],
    [(1, e7), (7, e1), (12, e1), (13, e1), (18, e1)],
    [(5, e3), (10, e1), (19, e1)],
    [(2, e5), (6, e2), (15, e1), (20, e1)],
    [(21, e1)],
    [(8, e3), (14, e1), (22, e1)],
    [(5, e5), (10, e2), (19, e1), (23, e1)],
    [(1, e3), (7, e6), (12, e3), (13, e3), (18, e1), (24, e1)],
    [(8, e5), (14, e2), (22, e1), (25, e1)]])
private theorem commutator_56_left_s1 : wordMatrix [Atom.root 10 2] = atomMatrix (Atom.root 10 2) := by simp
private theorem commutator_56_left_s0 : wordMatrix [Atom.root 4 1, Atom.root 10 2] = commutator_56_target := by
  rw [wordMatrix_cons, commutator_56_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 4 1))
  decide +kernel
private theorem commutator_56_left : wordMatrix [Atom.root 4 1, Atom.root 10 2] = commutator_56_target := commutator_56_left_s0
private theorem commutator_56_right_s1 : wordMatrix [Atom.root 4 1] = atomMatrix (Atom.root 4 1) := by simp
private theorem commutator_56_right_s0 : wordMatrix [Atom.root 10 2, Atom.root 4 1] = commutator_56_target := by
  rw [wordMatrix_cons, commutator_56_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 10 2))
  decide +kernel
private theorem commutator_56_right : wordMatrix [Atom.root 10 2, Atom.root 4 1] = commutator_56_target := commutator_56_right_s0
theorem commutator_56 : wordGroup (commutator_lhs 56) = wordGroup (commutator_rhs 56) := by
  apply word_eq_of_matrix_eq
  exact commutator_56_left.trans commutator_56_right.symm

private def commutator_57_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(0, e1), (3, e1)],
    [(4, e1)],
    [(5, e1)],
    [(2, e1), (6, e1)],
    [(1, e1), (7, e1)],
    [(8, e1)],
    [(9, e1)],
    [(5, e1), (10, e1)],
    [(0, e2), (3, e1), (11, e1)],
    [(1, e3), (7, e1), (12, e1)],
    [(1, e3), (7, e1), (13, e1)],
    [(8, e1), (14, e1)],
    [(2, e2), (6, e1), (15, e1)],
    [(16, e1)],
    [(0, e5), (3, e3), (11, e1), (17, e1)],
    [(1, e6), (7, e1), (12, e1), (13, e1), (18, e1)],
    [(5, e2), (10, e1), (19, e1)],
    [(2, e5), (6, e3), (15, e1), (20, e1)],
    [(21, e1)],
    [(8, e2), (14, e1), (22, e1)],
    [(5, e5), (10, e3), (19, e1), (23, e1)],
    [(1, e3), (7, e7), (12, e2), (13, e2), (18, e1), (24, e1)],
    [(8, e5), (14, e3), (22, e1), (25, e1)]])
private theorem commutator_57_left_s1 : wordMatrix [Atom.root 10 3] = atomMatrix (Atom.root 10 3) := by simp
private theorem commutator_57_left_s0 : wordMatrix [Atom.root 4 1, Atom.root 10 3] = commutator_57_target := by
  rw [wordMatrix_cons, commutator_57_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 4 1))
  decide +kernel
private theorem commutator_57_left : wordMatrix [Atom.root 4 1, Atom.root 10 3] = commutator_57_target := commutator_57_left_s0
private theorem commutator_57_right_s1 : wordMatrix [Atom.root 4 1] = atomMatrix (Atom.root 4 1) := by simp
private theorem commutator_57_right_s0 : wordMatrix [Atom.root 10 3, Atom.root 4 1] = commutator_57_target := by
  rw [wordMatrix_cons, commutator_57_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 10 3))
  decide +kernel
private theorem commutator_57_right : wordMatrix [Atom.root 10 3, Atom.root 4 1] = commutator_57_target := commutator_57_right_s0
theorem commutator_57 : wordGroup (commutator_lhs 57) = wordGroup (commutator_rhs 57) := by
  apply word_eq_of_matrix_eq
  exact commutator_57_left.trans commutator_57_right.symm

private def commutator_58_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(0, e1), (3, e1)],
    [(4, e1)],
    [(5, e1)],
    [(2, e1), (6, e1)],
    [(1, e1), (7, e1)],
    [(8, e1)],
    [(9, e1)],
    [(5, e1), (10, e1)],
    [(0, e5), (3, e1), (11, e1)],
    [(1, e4), (7, e1), (12, e1)],
    [(1, e4), (7, e1), (13, e1)],
    [(8, e1), (14, e1)],
    [(2, e5), (6, e1), (15, e1)],
    [(16, e1)],
    [(0, e7), (3, e4), (11, e1), (17, e1)],
    [(1, e3), (7, e1), (12, e1), (13, e1), (18, e1)],
    [(5, e5), (10, e1), (19, e1)],
    [(2, e7), (6, e4), (15, e1), (20, e1)],
    [(21, e1)],
    [(8, e5), (14, e1), (22, e1)],
    [(5, e7), (10, e4), (19, e1), (23, e1)],
    [(1, e5), (7, e2), (12, e5), (13, e5), (18, e1), (24, e1)],
    [(8, e7), (14, e4), (22, e1), (25, e1)]])
private theorem commutator_58_left_s1 : wordMatrix [Atom.root 10 4] = atomMatrix (Atom.root 10 4) := by simp
private theorem commutator_58_left_s0 : wordMatrix [Atom.root 4 1, Atom.root 10 4] = commutator_58_target := by
  rw [wordMatrix_cons, commutator_58_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 4 1))
  decide +kernel
private theorem commutator_58_left : wordMatrix [Atom.root 4 1, Atom.root 10 4] = commutator_58_target := commutator_58_left_s0
private theorem commutator_58_right_s1 : wordMatrix [Atom.root 4 1] = atomMatrix (Atom.root 4 1) := by simp
private theorem commutator_58_right_s0 : wordMatrix [Atom.root 10 4, Atom.root 4 1] = commutator_58_target := by
  rw [wordMatrix_cons, commutator_58_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 10 4))
  decide +kernel
private theorem commutator_58_right : wordMatrix [Atom.root 10 4, Atom.root 4 1] = commutator_58_target := commutator_58_right_s0
theorem commutator_58 : wordGroup (commutator_lhs 58) = wordGroup (commutator_rhs 58) := by
  apply word_eq_of_matrix_eq
  exact commutator_58_left.trans commutator_58_right.symm

private def commutator_59_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(0, e1), (3, e1)],
    [(4, e1)],
    [(5, e1)],
    [(2, e1), (6, e1)],
    [(1, e1), (7, e1)],
    [(8, e1)],
    [(9, e1)],
    [(5, e1), (10, e1)],
    [(0, e4), (3, e1), (11, e1)],
    [(1, e5), (7, e1), (12, e1)],
    [(1, e5), (7, e1), (13, e1)],
    [(8, e1), (14, e1)],
    [(2, e4), (6, e1), (15, e1)],
    [(16, e1)],
    [(0, e7), (3, e5), (11, e1), (17, e1)],
    [(1, e2), (7, e1), (12, e1), (13, e1), (18, e1)],
    [(5, e4), (10, e1), (19, e1)],
    [(2, e7), (6, e5), (15, e1), (20, e1)],
    [(21, e1)],
    [(8, e4), (14, e1), (22, e1)],
    [(5, e7), (10, e5), (19, e1), (23, e1)],
    [(1, e5), (7, e3), (12, e4), (13, e4), (18, e1), (24, e1)],
    [(8, e7), (14, e5), (22, e1), (25, e1)]])
private theorem commutator_59_left_s1 : wordMatrix [Atom.root 10 5] = atomMatrix (Atom.root 10 5) := by simp
private theorem commutator_59_left_s0 : wordMatrix [Atom.root 4 1, Atom.root 10 5] = commutator_59_target := by
  rw [wordMatrix_cons, commutator_59_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 4 1))
  decide +kernel
private theorem commutator_59_left : wordMatrix [Atom.root 4 1, Atom.root 10 5] = commutator_59_target := commutator_59_left_s0
private theorem commutator_59_right_s1 : wordMatrix [Atom.root 4 1] = atomMatrix (Atom.root 4 1) := by simp
private theorem commutator_59_right_s0 : wordMatrix [Atom.root 10 5, Atom.root 4 1] = commutator_59_target := by
  rw [wordMatrix_cons, commutator_59_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 10 5))
  decide +kernel
private theorem commutator_59_right : wordMatrix [Atom.root 10 5, Atom.root 4 1] = commutator_59_target := commutator_59_right_s0
theorem commutator_59 : wordGroup (commutator_lhs 59) = wordGroup (commutator_rhs 59) := by
  apply word_eq_of_matrix_eq
  exact commutator_59_left.trans commutator_59_right.symm

end Kourovka.Problem2153.WilsonModel.RootData.Relations
