import Kourovka.Problem2153.WilsonModel.RootData.Relations.Metadata
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
namespace Kourovka.Problem2153.WilsonModel.RootData.Relations
open Field8 F8
private def commutator_12_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(1, e1), (2, e1)],
    [(2, e1), (3, e1)],
    [(1, e1), (2, e1), (3, e1), (4, e1)],
    [(5, e1)],
    [(6, e1)],
    [(5, e1), (7, e1)],
    [(8, e1)],
    [(7, e1), (9, e1)],
    [(8, e1), (10, e1)],
    [(5, e1), (7, e1), (9, e1), (11, e1)],
    [(12, e1)],
    [(8, e1), (10, e1), (13, e1)],
    [(14, e1)],
    [(10, e1), (12, e1), (15, e1)],
    [(14, e1), (16, e1)],
    [(8, e1), (10, e1), (15, e1), (17, e1)],
    [(16, e1), (18, e1)],
    [(19, e1)],
    [(14, e1), (16, e1), (18, e1), (20, e1)],
    [(21, e1)],
    [(21, e1), (22, e1)],
    [(22, e1), (23, e1)],
    [(21, e1), (22, e1), (23, e1), (24, e1)],
    [(25, e1)]])
private theorem commutator_12_left_s1 : wordMatrix [Atom.root 3 1] = atomMatrix (Atom.root 3 1) := by simp
private theorem commutator_12_left_s0 : wordMatrix [Atom.root 1 1, Atom.root 3 1] = commutator_12_target := by
  rw [wordMatrix_cons, commutator_12_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 1 1))
  decide +kernel
private theorem commutator_12_left : wordMatrix [Atom.root 1 1, Atom.root 3 1] = commutator_12_target := commutator_12_left_s0
private theorem commutator_12_right_s1 : wordMatrix [Atom.root 1 1] = atomMatrix (Atom.root 1 1) := by simp
private theorem commutator_12_right_s0 : wordMatrix [Atom.root 3 1, Atom.root 1 1] = commutator_12_target := by
  rw [wordMatrix_cons, commutator_12_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 3 1))
  decide +kernel
private theorem commutator_12_right : wordMatrix [Atom.root 3 1, Atom.root 1 1] = commutator_12_target := commutator_12_right_s0
theorem commutator_12 : wordGroup (commutator_lhs 12) = wordGroup (commutator_rhs 12) := by
  apply word_eq_of_matrix_eq
  exact commutator_12_left.trans commutator_12_right.symm

private def commutator_13_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(1, e1), (2, e1)],
    [(1, e3), (2, e1), (3, e1)],
    [(1, e5), (2, e2), (3, e1), (4, e1)],
    [(5, e1)],
    [(6, e1)],
    [(5, e1), (7, e1)],
    [(8, e1)],
    [(5, e3), (7, e1), (9, e1)],
    [(8, e1), (10, e1)],
    [(5, e5), (7, e2), (9, e1), (11, e1)],
    [(12, e1)],
    [(8, e2), (10, e1), (13, e1)],
    [(14, e1)],
    [(8, e7), (10, e1), (12, e1), (15, e1)],
    [(14, e1), (16, e1)],
    [(8, e3), (10, e6), (12, e3), (15, e1), (17, e1)],
    [(14, e3), (16, e1), (18, e1)],
    [(19, e1)],
    [(14, e5), (16, e2), (18, e1), (20, e1)],
    [(21, e1)],
    [(21, e1), (22, e1)],
    [(21, e3), (22, e1), (23, e1)],
    [(21, e5), (22, e2), (23, e1), (24, e1)],
    [(25, e1)]])
private theorem commutator_13_left_s1 : wordMatrix [Atom.root 3 2] = atomMatrix (Atom.root 3 2) := by simp
private theorem commutator_13_left_s0 : wordMatrix [Atom.root 1 1, Atom.root 3 2] = commutator_13_target := by
  rw [wordMatrix_cons, commutator_13_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 1 1))
  decide +kernel
private theorem commutator_13_left : wordMatrix [Atom.root 1 1, Atom.root 3 2] = commutator_13_target := commutator_13_left_s0
private theorem commutator_13_right_s1 : wordMatrix [Atom.root 1 1] = atomMatrix (Atom.root 1 1) := by simp
private theorem commutator_13_right_s0 : wordMatrix [Atom.root 3 2, Atom.root 1 1] = commutator_13_target := by
  rw [wordMatrix_cons, commutator_13_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 3 2))
  decide +kernel
private theorem commutator_13_right : wordMatrix [Atom.root 3 2, Atom.root 1 1] = commutator_13_target := commutator_13_right_s0
theorem commutator_13 : wordGroup (commutator_lhs 13) = wordGroup (commutator_rhs 13) := by
  apply word_eq_of_matrix_eq
  exact commutator_13_left.trans commutator_13_right.symm

private def commutator_14_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(1, e1), (2, e1)],
    [(1, e2), (2, e1), (3, e1)],
    [(1, e5), (2, e3), (3, e1), (4, e1)],
    [(5, e1)],
    [(6, e1)],
    [(5, e1), (7, e1)],
    [(8, e1)],
    [(5, e2), (7, e1), (9, e1)],
    [(8, e1), (10, e1)],
    [(5, e5), (7, e3), (9, e1), (11, e1)],
    [(12, e1)],
    [(8, e3), (10, e1), (13, e1)],
    [(14, e1)],
    [(8, e6), (10, e1), (12, e1), (15, e1)],
    [(14, e1), (16, e1)],
    [(8, e3), (10, e7), (12, e2), (15, e1), (17, e1)],
    [(14, e2), (16, e1), (18, e1)],
    [(19, e1)],
    [(14, e5), (16, e3), (18, e1), (20, e1)],
    [(21, e1)],
    [(21, e1), (22, e1)],
    [(21, e2), (22, e1), (23, e1)],
    [(21, e5), (22, e3), (23, e1), (24, e1)],
    [(25, e1)]])
private theorem commutator_14_left_s1 : wordMatrix [Atom.root 3 3] = atomMatrix (Atom.root 3 3) := by simp
private theorem commutator_14_left_s0 : wordMatrix [Atom.root 1 1, Atom.root 3 3] = commutator_14_target := by
  rw [wordMatrix_cons, commutator_14_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 1 1))
  decide +kernel
private theorem commutator_14_left : wordMatrix [Atom.root 1 1, Atom.root 3 3] = commutator_14_target := commutator_14_left_s0
private theorem commutator_14_right_s1 : wordMatrix [Atom.root 1 1] = atomMatrix (Atom.root 1 1) := by simp
private theorem commutator_14_right_s0 : wordMatrix [Atom.root 3 3, Atom.root 1 1] = commutator_14_target := by
  rw [wordMatrix_cons, commutator_14_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 3 3))
  decide +kernel
private theorem commutator_14_right : wordMatrix [Atom.root 3 3, Atom.root 1 1] = commutator_14_target := commutator_14_right_s0
theorem commutator_14 : wordGroup (commutator_lhs 14) = wordGroup (commutator_rhs 14) := by
  apply word_eq_of_matrix_eq
  exact commutator_14_left.trans commutator_14_right.symm

private def commutator_15_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(1, e1), (2, e1)],
    [(1, e5), (2, e1), (3, e1)],
    [(1, e7), (2, e4), (3, e1), (4, e1)],
    [(5, e1)],
    [(6, e1)],
    [(5, e1), (7, e1)],
    [(8, e1)],
    [(5, e5), (7, e1), (9, e1)],
    [(8, e1), (10, e1)],
    [(5, e7), (7, e4), (9, e1), (11, e1)],
    [(12, e1)],
    [(8, e4), (10, e1), (13, e1)],
    [(14, e1)],
    [(8, e3), (10, e1), (12, e1), (15, e1)],
    [(14, e1), (16, e1)],
    [(8, e5), (10, e2), (12, e5), (15, e1), (17, e1)],
    [(14, e5), (16, e1), (18, e1)],
    [(19, e1)],
    [(14, e7), (16, e4), (18, e1), (20, e1)],
    [(21, e1)],
    [(21, e1), (22, e1)],
    [(21, e5), (22, e1), (23, e1)],
    [(21, e7), (22, e4), (23, e1), (24, e1)],
    [(25, e1)]])
private theorem commutator_15_left_s1 : wordMatrix [Atom.root 3 4] = atomMatrix (Atom.root 3 4) := by simp
private theorem commutator_15_left_s0 : wordMatrix [Atom.root 1 1, Atom.root 3 4] = commutator_15_target := by
  rw [wordMatrix_cons, commutator_15_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 1 1))
  decide +kernel
private theorem commutator_15_left : wordMatrix [Atom.root 1 1, Atom.root 3 4] = commutator_15_target := commutator_15_left_s0
private theorem commutator_15_right_s1 : wordMatrix [Atom.root 1 1] = atomMatrix (Atom.root 1 1) := by simp
private theorem commutator_15_right_s0 : wordMatrix [Atom.root 3 4, Atom.root 1 1] = commutator_15_target := by
  rw [wordMatrix_cons, commutator_15_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 3 4))
  decide +kernel
private theorem commutator_15_right : wordMatrix [Atom.root 3 4, Atom.root 1 1] = commutator_15_target := commutator_15_right_s0
theorem commutator_15 : wordGroup (commutator_lhs 15) = wordGroup (commutator_rhs 15) := by
  apply word_eq_of_matrix_eq
  exact commutator_15_left.trans commutator_15_right.symm

private def commutator_16_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(1, e1), (2, e1)],
    [(1, e4), (2, e1), (3, e1)],
    [(1, e7), (2, e5), (3, e1), (4, e1)],
    [(5, e1)],
    [(6, e1)],
    [(5, e1), (7, e1)],
    [(8, e1)],
    [(5, e4), (7, e1), (9, e1)],
    [(8, e1), (10, e1)],
    [(5, e7), (7, e5), (9, e1), (11, e1)],
    [(12, e1)],
    [(8, e5), (10, e1), (13, e1)],
    [(14, e1)],
    [(8, e2), (10, e1), (12, e1), (15, e1)],
    [(14, e1), (16, e1)],
    [(8, e5), (10, e3), (12, e4), (15, e1), (17, e1)],
    [(14, e4), (16, e1), (18, e1)],
    [(19, e1)],
    [(14, e7), (16, e5), (18, e1), (20, e1)],
    [(21, e1)],
    [(21, e1), (22, e1)],
    [(21, e4), (22, e1), (23, e1)],
    [(21, e7), (22, e5), (23, e1), (24, e1)],
    [(25, e1)]])
private theorem commutator_16_left_s1 : wordMatrix [Atom.root 3 5] = atomMatrix (Atom.root 3 5) := by simp
private theorem commutator_16_left_s0 : wordMatrix [Atom.root 1 1, Atom.root 3 5] = commutator_16_target := by
  rw [wordMatrix_cons, commutator_16_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 1 1))
  decide +kernel
private theorem commutator_16_left : wordMatrix [Atom.root 1 1, Atom.root 3 5] = commutator_16_target := commutator_16_left_s0
private theorem commutator_16_right_s1 : wordMatrix [Atom.root 1 1] = atomMatrix (Atom.root 1 1) := by simp
private theorem commutator_16_right_s0 : wordMatrix [Atom.root 3 5, Atom.root 1 1] = commutator_16_target := by
  rw [wordMatrix_cons, commutator_16_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 3 5))
  decide +kernel
private theorem commutator_16_right : wordMatrix [Atom.root 3 5, Atom.root 1 1] = commutator_16_target := commutator_16_right_s0
theorem commutator_16 : wordGroup (commutator_lhs 16) = wordGroup (commutator_rhs 16) := by
  apply word_eq_of_matrix_eq
  exact commutator_16_left.trans commutator_16_right.symm

private def commutator_17_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(1, e1), (2, e1)],
    [(1, e7), (2, e1), (3, e1)],
    [(1, e3), (2, e6), (3, e1), (4, e1)],
    [(5, e1)],
    [(6, e1)],
    [(5, e1), (7, e1)],
    [(8, e1)],
    [(5, e7), (7, e1), (9, e1)],
    [(8, e1), (10, e1)],
    [(5, e3), (7, e6), (9, e1), (11, e1)],
    [(12, e1)],
    [(8, e6), (10, e1), (13, e1)],
    [(14, e1)],
    [(8, e5), (10, e1), (12, e1), (15, e1)],
    [(14, e1), (16, e1)],
    [(8, e7), (10, e4), (12, e7), (15, e1), (17, e1)],
    [(14, e7), (16, e1), (18, e1)],
    [(19, e1)],
    [(14, e3), (16, e6), (18, e1), (20, e1)],
    [(21, e1)],
    [(21, e1), (22, e1)],
    [(21, e7), (22, e1), (23, e1)],
    [(21, e3), (22, e6), (23, e1), (24, e1)],
    [(25, e1)]])
private theorem commutator_17_left_s1 : wordMatrix [Atom.root 3 6] = atomMatrix (Atom.root 3 6) := by simp
private theorem commutator_17_left_s0 : wordMatrix [Atom.root 1 1, Atom.root 3 6] = commutator_17_target := by
  rw [wordMatrix_cons, commutator_17_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 1 1))
  decide +kernel
private theorem commutator_17_left : wordMatrix [Atom.root 1 1, Atom.root 3 6] = commutator_17_target := commutator_17_left_s0
private theorem commutator_17_right_s1 : wordMatrix [Atom.root 1 1] = atomMatrix (Atom.root 1 1) := by simp
private theorem commutator_17_right_s0 : wordMatrix [Atom.root 3 6, Atom.root 1 1] = commutator_17_target := by
  rw [wordMatrix_cons, commutator_17_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 3 6))
  decide +kernel
private theorem commutator_17_right : wordMatrix [Atom.root 3 6, Atom.root 1 1] = commutator_17_target := commutator_17_right_s0
theorem commutator_17 : wordGroup (commutator_lhs 17) = wordGroup (commutator_rhs 17) := by
  apply word_eq_of_matrix_eq
  exact commutator_17_left.trans commutator_17_right.symm

end Kourovka.Problem2153.WilsonModel.RootData.Relations
