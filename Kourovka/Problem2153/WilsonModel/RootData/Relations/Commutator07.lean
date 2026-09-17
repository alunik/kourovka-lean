import Kourovka.Problem2153.WilsonModel.RootData.Relations.Metadata
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
namespace Kourovka.Problem2153.WilsonModel.RootData.Relations
open Field8 F8
private def commutator_42_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(0, e1), (1, e1), (3, e1)],
    [(1, e1), (2, e1), (4, e1)],
    [(5, e1)],
    [(2, e1), (6, e1)],
    [(1, e1), (7, e1)],
    [(8, e1)],
    [(5, e1), (9, e1)],
    [(5, e1), (10, e1)],
    [(0, e1), (1, e1), (3, e1), (5, e1), (7, e1), (11, e1)],
    [(7, e1), (12, e1)],
    [(7, e1), (8, e1), (13, e1)],
    [(8, e1), (14, e1)],
    [(2, e1), (6, e1), (8, e1), (15, e1)],
    [(16, e1)],
    [(0, e1), (5, e1), (7, e1), (8, e1), (10, e1), (11, e1), (12, e1), (17, e1)],
    [(1, e1), (7, e1), (8, e1), (12, e1), (13, e1), (14, e1), (18, e1)],
    [(5, e1), (10, e1), (19, e1)],
    [(2, e1), (8, e1), (14, e1), (15, e1), (16, e1), (20, e1)],
    [(21, e1)],
    [(8, e1), (14, e1), (22, e1)],
    [(5, e1), (19, e1), (21, e1), (23, e1)],
    [(1, e1), (8, e1), (12, e1), (13, e1), (14, e1), (18, e1), (21, e1), (22, e1), (24, e1)],
    [(8, e1), (22, e1), (25, e1)]])
private theorem commutator_42_left_s1 : wordMatrix [Atom.root 4 1] = atomMatrix (Atom.root 4 1) := by simp
private theorem commutator_42_left_s0 : wordMatrix [Atom.root 3 1, Atom.root 4 1] = commutator_42_target := by
  rw [wordMatrix_cons, commutator_42_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 3 1))
  decide +kernel
private theorem commutator_42_left : wordMatrix [Atom.root 3 1, Atom.root 4 1] = commutator_42_target := commutator_42_left_s0
private theorem commutator_42_right_s1 : wordMatrix [Atom.root 3 1] = atomMatrix (Atom.root 3 1) := by simp
private theorem commutator_42_right_s0 : wordMatrix [Atom.root 4 1, Atom.root 3 1] = commutator_42_target := by
  rw [wordMatrix_cons, commutator_42_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 4 1))
  decide +kernel
private theorem commutator_42_right : wordMatrix [Atom.root 4 1, Atom.root 3 1] = commutator_42_target := commutator_42_right_s0
theorem commutator_42 : wordGroup (commutator_lhs 42) = wordGroup (commutator_rhs 42) := by
  apply word_eq_of_matrix_eq
  exact commutator_42_left.trans commutator_42_right.symm

private def commutator_43_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(1, e1), (3, e1)],
    [(0, e1), (1, e1), (2, e1), (4, e1)],
    [(5, e1)],
    [(1, e1), (6, e1)],
    [(7, e1)],
    [(8, e1)],
    [(1, e1), (5, e1), (9, e1)],
    [(10, e1)],
    [(2, e1), (5, e1), (7, e1), (11, e1)],
    [(5, e1), (12, e1)],
    [(8, e1), (13, e1)],
    [(14, e1)],
    [(7, e1), (8, e1), (15, e1)],
    [(8, e1), (16, e1)],
    [(1, e1), (5, e1), (6, e1), (8, e1), (9, e1), (10, e1), (12, e1), (17, e1)],
    [(10, e1), (14, e1), (18, e1)],
    [(8, e1), (19, e1)],
    [(5, e1), (8, e1), (13, e1), (14, e1), (16, e1), (20, e1)],
    [(21, e1)],
    [(22, e1)],
    [(14, e1), (21, e1), (23, e1)],
    [(8, e1), (16, e1), (19, e1), (21, e1), (22, e1), (24, e1)],
    [(21, e1), (25, e1)]])
private theorem commutator_43_left_s1 : wordMatrix [Atom.root 5 1] = atomMatrix (Atom.root 5 1) := by simp
private theorem commutator_43_left_s0 : wordMatrix [Atom.root 3 1, Atom.root 5 1] = commutator_43_target := by
  rw [wordMatrix_cons, commutator_43_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 3 1))
  decide +kernel
private theorem commutator_43_left : wordMatrix [Atom.root 3 1, Atom.root 5 1] = commutator_43_target := commutator_43_left_s0
private theorem commutator_43_right_s1 : wordMatrix [Atom.root 3 1] = atomMatrix (Atom.root 3 1) := by simp
private theorem commutator_43_right_s0 : wordMatrix [Atom.root 5 1, Atom.root 3 1] = commutator_43_target := by
  rw [wordMatrix_cons, commutator_43_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 5 1))
  decide +kernel
private theorem commutator_43_right : wordMatrix [Atom.root 5 1, Atom.root 3 1] = commutator_43_target := commutator_43_right_s0
theorem commutator_43 : wordGroup (commutator_lhs 43) = wordGroup (commutator_rhs 43) := by
  apply word_eq_of_matrix_eq
  exact commutator_43_left.trans commutator_43_right.symm

private def commutator_44_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(1, e1), (3, e1)],
    [(1, e1), (2, e1), (4, e1)],
    [(1, e1), (5, e1)],
    [(0, e1), (6, e1)],
    [(2, e1), (7, e1)],
    [(8, e1)],
    [(1, e1), (3, e1), (5, e1), (9, e1)],
    [(10, e1)],
    [(1, e1), (2, e1), (4, e1), (5, e1), (7, e1), (11, e1)],
    [(12, e1)],
    [(6, e1), (8, e1), (13, e1)],
    [(1, e1), (5, e1), (14, e1)],
    [(8, e1), (15, e1)],
    [(2, e1), (7, e1), (16, e1)],
    [(8, e1), (10, e1), (12, e1), (17, e1)],
    [(1, e1), (3, e1), (5, e1), (9, e1), (14, e1), (18, e1)],
    [(0, e1), (6, e1), (12, e1), (19, e1)],
    [(1, e1), (2, e1), (4, e1), (5, e1), (7, e1), (11, e1), (14, e1), (16, e1), (20, e1)],
    [(1, e1), (14, e1), (21, e1)],
    [(2, e1), (16, e1), (22, e1)],
    [(1, e1), (3, e1), (14, e1), (18, e1), (21, e1), (23, e1)],
    [(1, e1), (2, e1), (4, e1), (14, e1), (16, e1), (20, e1), (21, e1), (22, e1), (24, e1)],
    [(0, e1), (12, e1), (19, e1), (25, e1)]])
private theorem commutator_44_left_s1 : wordMatrix [Atom.root 6 1] = atomMatrix (Atom.root 6 1) := by simp
private theorem commutator_44_left_s0 : wordMatrix [Atom.root 3 1, Atom.root 6 1] = commutator_44_target := by
  rw [wordMatrix_cons, commutator_44_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 3 1))
  decide +kernel
private theorem commutator_44_left : wordMatrix [Atom.root 3 1, Atom.root 6 1] = commutator_44_target := commutator_44_left_s0
private theorem commutator_44_right_s1 : wordMatrix [Atom.root 3 1] = atomMatrix (Atom.root 3 1) := by simp
private theorem commutator_44_right_s0 : wordMatrix [Atom.root 6 1, Atom.root 3 1] = commutator_44_target := by
  rw [wordMatrix_cons, commutator_44_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 6 1))
  decide +kernel
private theorem commutator_44_right : wordMatrix [Atom.root 6 1, Atom.root 3 1] = commutator_44_target := commutator_44_right_s0
theorem commutator_44 : wordGroup (commutator_lhs 44) = wordGroup (commutator_rhs 44) := by
  apply word_eq_of_matrix_eq
  exact commutator_44_left.trans commutator_44_right.symm

private def commutator_45_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(1, e1), (3, e1)],
    [(1, e1), (2, e1), (4, e1)],
    [(0, e1), (5, e1)],
    [(6, e1)],
    [(7, e1)],
    [(0, e1), (2, e1), (8, e1)],
    [(0, e1), (5, e1), (9, e1)],
    [(3, e1), (10, e1)],
    [(0, e1), (5, e1), (7, e1), (11, e1)],
    [(4, e1), (12, e1)],
    [(0, e1), (2, e1), (4, e1), (8, e1), (13, e1)],
    [(3, e1), (6, e1), (14, e1)],
    [(0, e1), (2, e1), (8, e1), (15, e1)],
    [(4, e1), (16, e1)],
    [(0, e1), (2, e1), (3, e1), (4, e1), (8, e1), (10, e1), (12, e1), (17, e1)],
    [(3, e1), (6, e1), (14, e1), (18, e1)],
    [(11, e1), (19, e1)],
    [(3, e1), (4, e1), (6, e1), (14, e1), (16, e1), (20, e1)],
    [(4, e1), (9, e1), (12, e1), (13, e1), (21, e1)],
    [(11, e1), (15, e1), (22, e1)],
    [(4, e1), (9, e1), (12, e1), (13, e1), (17, e1), (21, e1), (23, e1)],
    [(4, e1), (9, e1), (11, e1), (12, e1), (13, e1), (15, e1), (21, e1), (22, e1), (24, e1)],
    [(17, e1), (20, e1), (25, e1)]])
private theorem commutator_45_left_s1 : wordMatrix [Atom.root 7 1] = atomMatrix (Atom.root 7 1) := by simp
private theorem commutator_45_left_s0 : wordMatrix [Atom.root 3 1, Atom.root 7 1] = commutator_45_target := by
  rw [wordMatrix_cons, commutator_45_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 3 1))
  decide +kernel
private theorem commutator_45_left : wordMatrix [Atom.root 3 1, Atom.root 7 1] = commutator_45_target := commutator_45_left_s0
private theorem commutator_45_right_s4 : wordMatrix [Atom.root 11 1] = atomMatrix (Atom.root 11 1) := by simp
private def commutator_45_right_m3 : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(5, e1)],
    [(6, e1)],
    [(7, e1)],
    [(8, e1)],
    [(9, e1)],
    [(10, e1)],
    [(0, e1), (11, e1)],
    [(1, e1), (12, e1)],
    [(0, e1), (1, e1), (13, e1)],
    [(1, e1), (14, e1)],
    [(2, e1), (15, e1)],
    [(2, e1), (16, e1)],
    [(0, e1), (3, e1), (17, e1)],
    [(1, e1), (3, e1), (18, e1)],
    [(0, e1), (5, e1), (19, e1)],
    [(2, e1), (4, e1), (6, e1), (20, e1)],
    [(1, e1), (5, e1), (21, e1)],
    [(2, e1), (7, e1), (8, e1), (22, e1)],
    [(3, e1), (5, e1), (9, e1), (10, e1), (23, e1)],
    [(0, e1), (1, e1), (4, e1), (7, e1), (11, e1), (12, e1), (13, e1), (24, e1)],
    [(0, e1), (1, e1), (6, e1), (8, e1), (12, e1), (14, e1), (25, e1)]])
private theorem commutator_45_right_s3 : wordMatrix [Atom.root 10 1, Atom.root 11 1] = commutator_45_right_m3 := by
  rw [wordMatrix_cons, commutator_45_right_s4]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 10 1))
  decide +kernel
private def commutator_45_right_m2 : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(5, e1)],
    [(6, e1)],
    [(7, e1)],
    [(8, e1)],
    [(0, e1), (9, e1)],
    [(1, e1), (10, e1)],
    [(0, e1), (11, e1)],
    [(1, e1), (2, e1), (12, e1)],
    [(0, e1), (1, e1), (13, e1)],
    [(1, e1), (14, e1)],
    [(0, e1), (2, e1), (15, e1)],
    [(1, e1), (2, e1), (16, e1)],
    [(0, e1), (3, e1), (4, e1), (17, e1)],
    [(1, e1), (3, e1), (6, e1), (18, e1)],
    [(0, e1), (5, e1), (7, e1), (19, e1)],
    [(2, e1), (3, e1), (4, e1), (6, e1), (20, e1)],
    [(1, e1), (5, e1), (8, e1), (21, e1)],
    [(2, e1), (5, e1), (7, e1), (8, e1), (22, e1)],
    [(0, e1), (1, e1), (2, e1), (3, e1), (5, e1), (9, e1), (10, e1), (13, e1), (23, e1)],
    [(1, e1), (2, e1), (4, e1), (7, e1), (9, e1), (11, e1), (12, e1), (13, e1), (15, e1), (24, e1)],
    [(0, e1), (2, e1), (6, e1), (8, e1), (10, e1), (12, e1), (14, e1), (16, e1), (25, e1)]])
private theorem commutator_45_right_s2 : wordMatrix [Atom.root 9 1, Atom.root 10 1, Atom.root 11 1] = commutator_45_right_m2 := by
  rw [wordMatrix_cons, commutator_45_right_s3]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 9 1))
  decide +kernel
private def commutator_45_right_m1 : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(1, e1), (3, e1)],
    [(1, e1), (2, e1), (4, e1)],
    [(5, e1)],
    [(6, e1)],
    [(7, e1)],
    [(8, e1)],
    [(0, e1), (5, e1), (9, e1)],
    [(1, e1), (10, e1)],
    [(0, e1), (5, e1), (7, e1), (11, e1)],
    [(1, e1), (2, e1), (12, e1)],
    [(0, e1), (1, e1), (8, e1), (13, e1)],
    [(1, e1), (14, e1)],
    [(0, e1), (2, e1), (8, e1), (15, e1)],
    [(1, e1), (2, e1), (16, e1)],
    [(0, e1), (2, e1), (3, e1), (4, e1), (8, e1), (10, e1), (12, e1), (17, e1)],
    [(3, e1), (6, e1), (14, e1), (18, e1)],
    [(0, e1), (5, e1), (7, e1), (19, e1)],
    [(3, e1), (4, e1), (6, e1), (14, e1), (16, e1), (20, e1)],
    [(1, e1), (5, e1), (8, e1), (21, e1)],
    [(2, e1), (5, e1), (7, e1), (8, e1), (22, e1)],
    [(0, e1), (2, e1), (3, e1), (8, e1), (9, e1), (10, e1), (13, e1), (21, e1), (23, e1)],
    [(4, e1), (9, e1), (11, e1), (12, e1), (13, e1), (15, e1), (21, e1), (22, e1), (24, e1)],
    [(0, e1), (2, e1), (6, e1), (8, e1), (10, e1), (12, e1), (14, e1), (16, e1), (25, e1)]])
private theorem commutator_45_right_s1 : wordMatrix [Atom.root 3 1, Atom.root 9 1, Atom.root 10 1, Atom.root 11 1] = commutator_45_right_m1 := by
  rw [wordMatrix_cons, commutator_45_right_s2]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 3 1))
  decide +kernel
private theorem commutator_45_right_s0 : wordMatrix [Atom.root 7 1, Atom.root 3 1, Atom.root 9 1, Atom.root 10 1, Atom.root 11 1] = commutator_45_target := by
  rw [wordMatrix_cons, commutator_45_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 7 1))
  decide +kernel
private theorem commutator_45_right : wordMatrix [Atom.root 7 1, Atom.root 3 1, Atom.root 9 1, Atom.root 10 1, Atom.root 11 1] = commutator_45_target := commutator_45_right_s0
theorem commutator_45 : wordGroup (commutator_lhs 45) = wordGroup (commutator_rhs 45) := by
  apply word_eq_of_matrix_eq
  exact commutator_45_left.trans commutator_45_right.symm

private def commutator_46_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(1, e1), (3, e1)],
    [(1, e1), (2, e1), (4, e1)],
    [(5, e1)],
    [(6, e1)],
    [(0, e1), (7, e1)],
    [(1, e1), (8, e1)],
    [(5, e1), (9, e1)],
    [(0, e1), (10, e1)],
    [(0, e1), (5, e1), (7, e1), (11, e1)],
    [(3, e1), (12, e1)],
    [(1, e1), (8, e1), (13, e1)],
    [(2, e1), (14, e1)],
    [(1, e1), (4, e1), (8, e1), (15, e1)],
    [(6, e1), (16, e1)],
    [(0, e1), (1, e1), (3, e1), (8, e1), (10, e1), (12, e1), (17, e1)],
    [(2, e1), (4, e1), (14, e1), (18, e1)],
    [(9, e1), (19, e1)],
    [(2, e1), (6, e1), (14, e1), (16, e1), (20, e1)],
    [(0, e1), (7, e1), (10, e1), (21, e1)],
    [(3, e1), (13, e1), (22, e1)],
    [(0, e1), (7, e1), (10, e1), (11, e1), (21, e1), (23, e1)],
    [(0, e1), (3, e1), (7, e1), (10, e1), (13, e1), (17, e1), (21, e1), (22, e1), (24, e1)],
    [(4, e1), (15, e1), (18, e1), (25, e1)]])
private theorem commutator_46_left_s1 : wordMatrix [Atom.root 8 1] = atomMatrix (Atom.root 8 1) := by simp
private theorem commutator_46_left_s0 : wordMatrix [Atom.root 3 1, Atom.root 8 1] = commutator_46_target := by
  rw [wordMatrix_cons, commutator_46_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 3 1))
  decide +kernel
private theorem commutator_46_left : wordMatrix [Atom.root 3 1, Atom.root 8 1] = commutator_46_target := commutator_46_left_s0
private theorem commutator_46_right_s2 : wordMatrix [Atom.root 10 1] = atomMatrix (Atom.root 10 1) := by simp
private def commutator_46_right_m1 : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(1, e1), (3, e1)],
    [(1, e1), (2, e1), (4, e1)],
    [(5, e1)],
    [(6, e1)],
    [(7, e1)],
    [(8, e1)],
    [(5, e1), (9, e1)],
    [(10, e1)],
    [(0, e1), (5, e1), (7, e1), (11, e1)],
    [(1, e1), (12, e1)],
    [(1, e1), (8, e1), (13, e1)],
    [(14, e1)],
    [(2, e1), (8, e1), (15, e1)],
    [(16, e1)],
    [(0, e1), (1, e1), (3, e1), (8, e1), (10, e1), (12, e1), (17, e1)],
    [(1, e1), (14, e1), (18, e1)],
    [(5, e1), (19, e1)],
    [(2, e1), (6, e1), (14, e1), (16, e1), (20, e1)],
    [(21, e1)],
    [(8, e1), (22, e1)],
    [(5, e1), (10, e1), (21, e1), (23, e1)],
    [(1, e1), (7, e1), (8, e1), (12, e1), (13, e1), (21, e1), (22, e1), (24, e1)],
    [(8, e1), (14, e1), (25, e1)]])
private theorem commutator_46_right_s1 : wordMatrix [Atom.root 3 1, Atom.root 10 1] = commutator_46_right_m1 := by
  rw [wordMatrix_cons, commutator_46_right_s2]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 3 1))
  decide +kernel
private theorem commutator_46_right_s0 : wordMatrix [Atom.root 8 1, Atom.root 3 1, Atom.root 10 1] = commutator_46_target := by
  rw [wordMatrix_cons, commutator_46_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 8 1))
  decide +kernel
private theorem commutator_46_right : wordMatrix [Atom.root 8 1, Atom.root 3 1, Atom.root 10 1] = commutator_46_target := commutator_46_right_s0
theorem commutator_46 : wordGroup (commutator_lhs 46) = wordGroup (commutator_rhs 46) := by
  apply word_eq_of_matrix_eq
  exact commutator_46_left.trans commutator_46_right.symm

private def commutator_47_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(1, e1), (3, e1)],
    [(1, e1), (2, e1), (4, e1)],
    [(5, e1)],
    [(6, e1)],
    [(7, e1)],
    [(8, e1)],
    [(0, e1), (5, e1), (9, e1)],
    [(1, e1), (10, e1)],
    [(5, e1), (7, e1), (11, e1)],
    [(2, e1), (12, e1)],
    [(8, e1), (13, e1)],
    [(14, e1)],
    [(0, e1), (8, e1), (15, e1)],
    [(1, e1), (16, e1)],
    [(1, e1), (2, e1), (4, e1), (8, e1), (10, e1), (12, e1), (17, e1)],
    [(6, e1), (14, e1), (18, e1)],
    [(7, e1), (19, e1)],
    [(1, e1), (3, e1), (14, e1), (16, e1), (20, e1)],
    [(8, e1), (21, e1)],
    [(5, e1), (22, e1)],
    [(2, e1), (8, e1), (13, e1), (21, e1), (23, e1)],
    [(0, e1), (5, e1), (8, e1), (9, e1), (15, e1), (21, e1), (22, e1), (24, e1)],
    [(1, e1), (10, e1), (16, e1), (25, e1)]])
private theorem commutator_47_left_s1 : wordMatrix [Atom.root 9 1] = atomMatrix (Atom.root 9 1) := by simp
private theorem commutator_47_left_s0 : wordMatrix [Atom.root 3 1, Atom.root 9 1] = commutator_47_target := by
  rw [wordMatrix_cons, commutator_47_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 3 1))
  decide +kernel
private theorem commutator_47_left : wordMatrix [Atom.root 3 1, Atom.root 9 1] = commutator_47_target := commutator_47_left_s0
private theorem commutator_47_right_s1 : wordMatrix [Atom.root 3 1] = atomMatrix (Atom.root 3 1) := by simp
private theorem commutator_47_right_s0 : wordMatrix [Atom.root 9 1, Atom.root 3 1] = commutator_47_target := by
  rw [wordMatrix_cons, commutator_47_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 9 1))
  decide +kernel
private theorem commutator_47_right : wordMatrix [Atom.root 9 1, Atom.root 3 1] = commutator_47_target := commutator_47_right_s0
theorem commutator_47 : wordGroup (commutator_lhs 47) = wordGroup (commutator_rhs 47) := by
  apply word_eq_of_matrix_eq
  exact commutator_47_left.trans commutator_47_right.symm

end Kourovka.Problem2153.WilsonModel.RootData.Relations
