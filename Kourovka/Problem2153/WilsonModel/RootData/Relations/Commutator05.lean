import Kourovka.Problem2153.WilsonModel.RootData.Relations.Metadata
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
namespace Kourovka.Problem2153.WilsonModel.RootData.Relations
open Field8 F8
private def commutator_30_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(0, e1), (2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(0, e1), (1, e1), (2, e1), (5, e1)],
    [(0, e1), (3, e1), (6, e1)],
    [(2, e1), (7, e1)],
    [(0, e1), (1, e1), (5, e1), (8, e1)],
    [(3, e1), (4, e1), (9, e1)],
    [(0, e1), (3, e1), (6, e1), (10, e1)],
    [(4, e1), (11, e1)],
    [(3, e1), (9, e1), (12, e1)],
    [(3, e1), (6, e1), (9, e1), (13, e1)],
    [(1, e1), (3, e1), (5, e1), (10, e1), (14, e1)],
    [(4, e1), (11, e1), (15, e1)],
    [(2, e1), (3, e1), (4, e1), (6, e1), (7, e1), (9, e1), (12, e1), (13, e1), (16, e1)],
    [(17, e1)],
    [(3, e1), (9, e1), (18, e1)],
    [(0, e1), (4, e1), (6, e1), (11, e1), (12, e1), (15, e1), (19, e1)],
    [(4, e1), (11, e1), (17, e1), (20, e1)],
    [(1, e1), (2, e1), (4, e1), (6, e1), (7, e1), (12, e1), (13, e1), (14, e1), (16, e1), (21, e1)],
    [(0, e1), (2, e1), (4, e1), (6, e1), (11, e1), (12, e1), (16, e1), (19, e1), (22, e1)],
    [(3, e1), (4, e1), (11, e1), (17, e1), (18, e1), (20, e1), (23, e1)],
    [(4, e1), (20, e1), (24, e1)],
    [(0, e1), (3, e1), (12, e1), (17, e1), (18, e1), (19, e1), (23, e1), (25, e1)]])
private theorem commutator_30_left_s1 : wordMatrix [Atom.root 6 1] = atomMatrix (Atom.root 6 1) := by simp
private theorem commutator_30_left_s0 : wordMatrix [Atom.root 2 1, Atom.root 6 1] = commutator_30_target := by
  rw [wordMatrix_cons, commutator_30_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 2 1))
  decide +kernel
private theorem commutator_30_left : wordMatrix [Atom.root 2 1, Atom.root 6 1] = commutator_30_target := commutator_30_left_s0
private theorem commutator_30_right_s2 : wordMatrix [Atom.root 8 1] = atomMatrix (Atom.root 8 1) := by simp
private def commutator_30_right_m1 : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(0, e1), (2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(0, e1), (2, e1), (5, e1)],
    [(3, e1), (6, e1)],
    [(0, e1), (7, e1)],
    [(0, e1), (1, e1), (5, e1), (8, e1)],
    [(4, e1), (9, e1)],
    [(0, e1), (3, e1), (6, e1), (10, e1)],
    [(11, e1)],
    [(3, e1), (9, e1), (12, e1)],
    [(9, e1), (13, e1)],
    [(0, e1), (2, e1), (3, e1), (10, e1), (14, e1)],
    [(4, e1), (11, e1), (15, e1)],
    [(3, e1), (4, e1), (6, e1), (9, e1), (12, e1), (13, e1), (16, e1)],
    [(17, e1)],
    [(4, e1), (18, e1)],
    [(4, e1), (9, e1), (11, e1), (15, e1), (19, e1)],
    [(17, e1), (20, e1)],
    [(0, e1), (3, e1), (4, e1), (6, e1), (7, e1), (10, e1), (12, e1), (13, e1), (16, e1), (21, e1)],
    [(3, e1), (9, e1), (11, e1), (13, e1), (19, e1), (22, e1)],
    [(11, e1), (17, e1), (20, e1), (23, e1)],
    [(17, e1), (24, e1)],
    [(4, e1), (11, e1), (15, e1), (17, e1), (18, e1), (23, e1), (25, e1)]])
private theorem commutator_30_right_s1 : wordMatrix [Atom.root 2 1, Atom.root 8 1] = commutator_30_right_m1 := by
  rw [wordMatrix_cons, commutator_30_right_s2]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 2 1))
  decide +kernel
private theorem commutator_30_right_s0 : wordMatrix [Atom.root 6 1, Atom.root 2 1, Atom.root 8 1] = commutator_30_target := by
  rw [wordMatrix_cons, commutator_30_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 6 1))
  decide +kernel
private theorem commutator_30_right : wordMatrix [Atom.root 6 1, Atom.root 2 1, Atom.root 8 1] = commutator_30_target := commutator_30_right_s0
theorem commutator_30 : wordGroup (commutator_lhs 30) = wordGroup (commutator_rhs 30) := by
  apply word_eq_of_matrix_eq
  exact commutator_30_left.trans commutator_30_right.symm

private def commutator_31_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(0, e1), (2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(2, e1), (5, e1)],
    [(3, e1), (6, e1)],
    [(7, e1)],
    [(0, e1), (2, e1), (5, e1), (8, e1)],
    [(4, e1), (9, e1)],
    [(6, e1), (10, e1)],
    [(11, e1)],
    [(4, e1), (9, e1), (12, e1)],
    [(4, e1), (9, e1), (13, e1)],
    [(3, e1), (6, e1), (10, e1), (14, e1)],
    [(11, e1), (15, e1)],
    [(9, e1), (12, e1), (13, e1), (16, e1)],
    [(17, e1)],
    [(18, e1)],
    [(15, e1), (19, e1)],
    [(17, e1), (20, e1)],
    [(4, e1), (9, e1), (16, e1), (21, e1)],
    [(11, e1), (15, e1), (19, e1), (22, e1)],
    [(20, e1), (23, e1)],
    [(24, e1)],
    [(17, e1), (20, e1), (23, e1), (25, e1)]])
private theorem commutator_31_left_s1 : wordMatrix [Atom.root 7 1] = atomMatrix (Atom.root 7 1) := by simp
private theorem commutator_31_left_s0 : wordMatrix [Atom.root 2 1, Atom.root 7 1] = commutator_31_target := by
  rw [wordMatrix_cons, commutator_31_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 2 1))
  decide +kernel
private theorem commutator_31_left : wordMatrix [Atom.root 2 1, Atom.root 7 1] = commutator_31_target := commutator_31_left_s0
private theorem commutator_31_right_s1 : wordMatrix [Atom.root 2 1] = atomMatrix (Atom.root 2 1) := by simp
private theorem commutator_31_right_s0 : wordMatrix [Atom.root 7 1, Atom.root 2 1] = commutator_31_target := by
  rw [wordMatrix_cons, commutator_31_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 7 1))
  decide +kernel
private theorem commutator_31_right : wordMatrix [Atom.root 7 1, Atom.root 2 1] = commutator_31_target := commutator_31_right_s0
theorem commutator_31 : wordGroup (commutator_lhs 31) = wordGroup (commutator_rhs 31) := by
  apply word_eq_of_matrix_eq
  exact commutator_31_left.trans commutator_31_right.symm

private def commutator_32_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(0, e1), (2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(0, e3), (2, e1), (5, e1)],
    [(3, e1), (6, e1)],
    [(7, e1)],
    [(0, e5), (2, e2), (5, e1), (8, e1)],
    [(4, e1), (9, e1)],
    [(3, e3), (6, e1), (10, e1)],
    [(11, e1)],
    [(4, e2), (9, e1), (12, e1)],
    [(4, e2), (9, e1), (13, e1)],
    [(3, e5), (6, e2), (10, e1), (14, e1)],
    [(11, e1), (15, e1)],
    [(4, e7), (9, e1), (12, e1), (13, e1), (16, e1)],
    [(17, e1)],
    [(18, e1)],
    [(11, e3), (15, e1), (19, e1)],
    [(17, e1), (20, e1)],
    [(4, e3), (9, e6), (12, e3), (13, e3), (16, e1), (21, e1)],
    [(11, e5), (15, e2), (19, e1), (22, e1)],
    [(17, e3), (20, e1), (23, e1)],
    [(24, e1)],
    [(17, e5), (20, e2), (23, e1), (25, e1)]])
private theorem commutator_32_left_s1 : wordMatrix [Atom.root 7 2] = atomMatrix (Atom.root 7 2) := by simp
private theorem commutator_32_left_s0 : wordMatrix [Atom.root 2 1, Atom.root 7 2] = commutator_32_target := by
  rw [wordMatrix_cons, commutator_32_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 2 1))
  decide +kernel
private theorem commutator_32_left : wordMatrix [Atom.root 2 1, Atom.root 7 2] = commutator_32_target := commutator_32_left_s0
private theorem commutator_32_right_s1 : wordMatrix [Atom.root 2 1] = atomMatrix (Atom.root 2 1) := by simp
private theorem commutator_32_right_s0 : wordMatrix [Atom.root 7 2, Atom.root 2 1] = commutator_32_target := by
  rw [wordMatrix_cons, commutator_32_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 7 2))
  decide +kernel
private theorem commutator_32_right : wordMatrix [Atom.root 7 2, Atom.root 2 1] = commutator_32_target := commutator_32_right_s0
theorem commutator_32 : wordGroup (commutator_lhs 32) = wordGroup (commutator_rhs 32) := by
  apply word_eq_of_matrix_eq
  exact commutator_32_left.trans commutator_32_right.symm

private def commutator_33_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(0, e1), (2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(0, e2), (2, e1), (5, e1)],
    [(3, e1), (6, e1)],
    [(7, e1)],
    [(0, e5), (2, e3), (5, e1), (8, e1)],
    [(4, e1), (9, e1)],
    [(3, e2), (6, e1), (10, e1)],
    [(11, e1)],
    [(4, e3), (9, e1), (12, e1)],
    [(4, e3), (9, e1), (13, e1)],
    [(3, e5), (6, e3), (10, e1), (14, e1)],
    [(11, e1), (15, e1)],
    [(4, e6), (9, e1), (12, e1), (13, e1), (16, e1)],
    [(17, e1)],
    [(18, e1)],
    [(11, e2), (15, e1), (19, e1)],
    [(17, e1), (20, e1)],
    [(4, e3), (9, e7), (12, e2), (13, e2), (16, e1), (21, e1)],
    [(11, e5), (15, e3), (19, e1), (22, e1)],
    [(17, e2), (20, e1), (23, e1)],
    [(24, e1)],
    [(17, e5), (20, e3), (23, e1), (25, e1)]])
private theorem commutator_33_left_s1 : wordMatrix [Atom.root 7 3] = atomMatrix (Atom.root 7 3) := by simp
private theorem commutator_33_left_s0 : wordMatrix [Atom.root 2 1, Atom.root 7 3] = commutator_33_target := by
  rw [wordMatrix_cons, commutator_33_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 2 1))
  decide +kernel
private theorem commutator_33_left : wordMatrix [Atom.root 2 1, Atom.root 7 3] = commutator_33_target := commutator_33_left_s0
private theorem commutator_33_right_s1 : wordMatrix [Atom.root 2 1] = atomMatrix (Atom.root 2 1) := by simp
private theorem commutator_33_right_s0 : wordMatrix [Atom.root 7 3, Atom.root 2 1] = commutator_33_target := by
  rw [wordMatrix_cons, commutator_33_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 7 3))
  decide +kernel
private theorem commutator_33_right : wordMatrix [Atom.root 7 3, Atom.root 2 1] = commutator_33_target := commutator_33_right_s0
theorem commutator_33 : wordGroup (commutator_lhs 33) = wordGroup (commutator_rhs 33) := by
  apply word_eq_of_matrix_eq
  exact commutator_33_left.trans commutator_33_right.symm

private def commutator_34_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(0, e1), (2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(0, e5), (2, e1), (5, e1)],
    [(3, e1), (6, e1)],
    [(7, e1)],
    [(0, e7), (2, e4), (5, e1), (8, e1)],
    [(4, e1), (9, e1)],
    [(3, e5), (6, e1), (10, e1)],
    [(11, e1)],
    [(4, e4), (9, e1), (12, e1)],
    [(4, e4), (9, e1), (13, e1)],
    [(3, e7), (6, e4), (10, e1), (14, e1)],
    [(11, e1), (15, e1)],
    [(4, e3), (9, e1), (12, e1), (13, e1), (16, e1)],
    [(17, e1)],
    [(18, e1)],
    [(11, e5), (15, e1), (19, e1)],
    [(17, e1), (20, e1)],
    [(4, e5), (9, e2), (12, e5), (13, e5), (16, e1), (21, e1)],
    [(11, e7), (15, e4), (19, e1), (22, e1)],
    [(17, e5), (20, e1), (23, e1)],
    [(24, e1)],
    [(17, e7), (20, e4), (23, e1), (25, e1)]])
private theorem commutator_34_left_s1 : wordMatrix [Atom.root 7 4] = atomMatrix (Atom.root 7 4) := by simp
private theorem commutator_34_left_s0 : wordMatrix [Atom.root 2 1, Atom.root 7 4] = commutator_34_target := by
  rw [wordMatrix_cons, commutator_34_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 2 1))
  decide +kernel
private theorem commutator_34_left : wordMatrix [Atom.root 2 1, Atom.root 7 4] = commutator_34_target := commutator_34_left_s0
private theorem commutator_34_right_s1 : wordMatrix [Atom.root 2 1] = atomMatrix (Atom.root 2 1) := by simp
private theorem commutator_34_right_s0 : wordMatrix [Atom.root 7 4, Atom.root 2 1] = commutator_34_target := by
  rw [wordMatrix_cons, commutator_34_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 7 4))
  decide +kernel
private theorem commutator_34_right : wordMatrix [Atom.root 7 4, Atom.root 2 1] = commutator_34_target := commutator_34_right_s0
theorem commutator_34 : wordGroup (commutator_lhs 34) = wordGroup (commutator_rhs 34) := by
  apply word_eq_of_matrix_eq
  exact commutator_34_left.trans commutator_34_right.symm

private def commutator_35_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(0, e1), (2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(0, e4), (2, e1), (5, e1)],
    [(3, e1), (6, e1)],
    [(7, e1)],
    [(0, e7), (2, e5), (5, e1), (8, e1)],
    [(4, e1), (9, e1)],
    [(3, e4), (6, e1), (10, e1)],
    [(11, e1)],
    [(4, e5), (9, e1), (12, e1)],
    [(4, e5), (9, e1), (13, e1)],
    [(3, e7), (6, e5), (10, e1), (14, e1)],
    [(11, e1), (15, e1)],
    [(4, e2), (9, e1), (12, e1), (13, e1), (16, e1)],
    [(17, e1)],
    [(18, e1)],
    [(11, e4), (15, e1), (19, e1)],
    [(17, e1), (20, e1)],
    [(4, e5), (9, e3), (12, e4), (13, e4), (16, e1), (21, e1)],
    [(11, e7), (15, e5), (19, e1), (22, e1)],
    [(17, e4), (20, e1), (23, e1)],
    [(24, e1)],
    [(17, e7), (20, e5), (23, e1), (25, e1)]])
private theorem commutator_35_left_s1 : wordMatrix [Atom.root 7 5] = atomMatrix (Atom.root 7 5) := by simp
private theorem commutator_35_left_s0 : wordMatrix [Atom.root 2 1, Atom.root 7 5] = commutator_35_target := by
  rw [wordMatrix_cons, commutator_35_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 2 1))
  decide +kernel
private theorem commutator_35_left : wordMatrix [Atom.root 2 1, Atom.root 7 5] = commutator_35_target := commutator_35_left_s0
private theorem commutator_35_right_s1 : wordMatrix [Atom.root 2 1] = atomMatrix (Atom.root 2 1) := by simp
private theorem commutator_35_right_s0 : wordMatrix [Atom.root 7 5, Atom.root 2 1] = commutator_35_target := by
  rw [wordMatrix_cons, commutator_35_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 7 5))
  decide +kernel
private theorem commutator_35_right : wordMatrix [Atom.root 7 5, Atom.root 2 1] = commutator_35_target := commutator_35_right_s0
theorem commutator_35 : wordGroup (commutator_lhs 35) = wordGroup (commutator_rhs 35) := by
  apply word_eq_of_matrix_eq
  exact commutator_35_left.trans commutator_35_right.symm

end Kourovka.Problem2153.WilsonModel.RootData.Relations
