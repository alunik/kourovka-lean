import Kourovka.Problem2153.WilsonModel.RootData.Relations.Metadata
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
namespace Kourovka.Problem2153.WilsonModel.RootData.Relations
open Field8 F8
private def commutator_18_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(1, e1), (2, e1)],
    [(1, e6), (2, e1), (3, e1)],
    [(1, e3), (2, e7), (3, e1), (4, e1)],
    [(5, e1)],
    [(6, e1)],
    [(5, e1), (7, e1)],
    [(8, e1)],
    [(5, e6), (7, e1), (9, e1)],
    [(8, e1), (10, e1)],
    [(5, e3), (7, e7), (9, e1), (11, e1)],
    [(12, e1)],
    [(8, e7), (10, e1), (13, e1)],
    [(14, e1)],
    [(8, e4), (10, e1), (12, e1), (15, e1)],
    [(14, e1), (16, e1)],
    [(8, e7), (10, e5), (12, e6), (15, e1), (17, e1)],
    [(14, e6), (16, e1), (18, e1)],
    [(19, e1)],
    [(14, e3), (16, e7), (18, e1), (20, e1)],
    [(21, e1)],
    [(21, e1), (22, e1)],
    [(21, e6), (22, e1), (23, e1)],
    [(21, e3), (22, e7), (23, e1), (24, e1)],
    [(25, e1)]])
private theorem commutator_18_left_s1 : wordMatrix [Atom.root 3 7] = atomMatrix (Atom.root 3 7) := by simp
private theorem commutator_18_left_s0 : wordMatrix [Atom.root 1 1, Atom.root 3 7] = commutator_18_target := by
  rw [wordMatrix_cons, commutator_18_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 1 1))
  decide +kernel
private theorem commutator_18_left : wordMatrix [Atom.root 1 1, Atom.root 3 7] = commutator_18_target := commutator_18_left_s0
private theorem commutator_18_right_s1 : wordMatrix [Atom.root 1 1] = atomMatrix (Atom.root 1 1) := by simp
private theorem commutator_18_right_s0 : wordMatrix [Atom.root 3 7, Atom.root 1 1] = commutator_18_target := by
  rw [wordMatrix_cons, commutator_18_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 3 7))
  decide +kernel
private theorem commutator_18_right : wordMatrix [Atom.root 3 7, Atom.root 1 1] = commutator_18_target := commutator_18_right_s0
theorem commutator_18 : wordGroup (commutator_lhs 18) = wordGroup (commutator_rhs 18) := by
  apply word_eq_of_matrix_eq
  exact commutator_18_left.trans commutator_18_right.symm

private def commutator_19_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(1, e1), (2, e1)],
    [(0, e1), (1, e1), (2, e1), (3, e1)],
    [(0, e1), (1, e1), (3, e1), (4, e1)],
    [(5, e1)],
    [(2, e1), (6, e1)],
    [(1, e1), (5, e1), (7, e1)],
    [(8, e1)],
    [(1, e1), (5, e1), (7, e1), (9, e1)],
    [(5, e1), (8, e1), (10, e1)],
    [(0, e1), (3, e1), (5, e1), (9, e1), (11, e1)],
    [(7, e1), (12, e1)],
    [(5, e1), (7, e1), (10, e1), (13, e1)],
    [(8, e1), (14, e1)],
    [(2, e1), (5, e1), (6, e1), (7, e1), (8, e1), (10, e1), (12, e1), (15, e1)],
    [(8, e1), (14, e1), (16, e1)],
    [(0, e1), (2, e1), (6, e1), (7, e1), (8, e1), (11, e1), (12, e1), (15, e1), (17, e1)],
    [(1, e1), (7, e1), (8, e1), (12, e1), (13, e1), (14, e1), (16, e1), (18, e1)],
    [(5, e1), (10, e1), (19, e1)],
    [(1, e1), (2, e1), (7, e1), (8, e1), (12, e1), (13, e1), (14, e1), (15, e1), (18, e1), (20, e1)],
    [(21, e1)],
    [(8, e1), (14, e1), (21, e1), (22, e1)],
    [(5, e1), (8, e1), (14, e1), (19, e1), (21, e1), (22, e1), (23, e1)],
    [(1, e1), (5, e1), (12, e1), (13, e1), (18, e1), (19, e1), (21, e1), (23, e1), (24, e1)],
    [(8, e1), (22, e1), (25, e1)]])
private theorem commutator_19_left_s1 : wordMatrix [Atom.root 4 1] = atomMatrix (Atom.root 4 1) := by simp
private theorem commutator_19_left_s0 : wordMatrix [Atom.root 1 1, Atom.root 4 1] = commutator_19_target := by
  rw [wordMatrix_cons, commutator_19_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 1 1))
  decide +kernel
private theorem commutator_19_left : wordMatrix [Atom.root 1 1, Atom.root 4 1] = commutator_19_target := commutator_19_left_s0
private theorem commutator_19_right_s2 : wordMatrix [Atom.root 5 1] = atomMatrix (Atom.root 5 1) := by simp
private def commutator_19_right_m1 : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(1, e1), (2, e1)],
    [(1, e1), (2, e1), (3, e1)],
    [(0, e1), (1, e1), (3, e1), (4, e1)],
    [(5, e1)],
    [(1, e1), (6, e1)],
    [(5, e1), (7, e1)],
    [(8, e1)],
    [(1, e1), (5, e1), (7, e1), (9, e1)],
    [(8, e1), (10, e1)],
    [(1, e1), (2, e1), (5, e1), (9, e1), (11, e1)],
    [(5, e1), (12, e1)],
    [(10, e1), (13, e1)],
    [(14, e1)],
    [(5, e1), (7, e1), (8, e1), (10, e1), (12, e1), (15, e1)],
    [(8, e1), (14, e1), (16, e1)],
    [(1, e1), (5, e1), (6, e1), (7, e1), (8, e1), (9, e1), (12, e1), (15, e1), (17, e1)],
    [(8, e1), (10, e1), (14, e1), (16, e1), (18, e1)],
    [(8, e1), (19, e1)],
    [(5, e1), (10, e1), (13, e1), (14, e1), (18, e1), (20, e1)],
    [(21, e1)],
    [(21, e1), (22, e1)],
    [(14, e1), (21, e1), (22, e1), (23, e1)],
    [(8, e1), (14, e1), (16, e1), (19, e1), (21, e1), (23, e1), (24, e1)],
    [(21, e1), (25, e1)]])
private theorem commutator_19_right_s1 : wordMatrix [Atom.root 1 1, Atom.root 5 1] = commutator_19_right_m1 := by
  rw [wordMatrix_cons, commutator_19_right_s2]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 1 1))
  decide +kernel
private theorem commutator_19_right_s0 : wordMatrix [Atom.root 4 1, Atom.root 1 1, Atom.root 5 1] = commutator_19_target := by
  rw [wordMatrix_cons, commutator_19_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 4 1))
  decide +kernel
private theorem commutator_19_right : wordMatrix [Atom.root 4 1, Atom.root 1 1, Atom.root 5 1] = commutator_19_target := commutator_19_right_s0
theorem commutator_19 : wordGroup (commutator_lhs 19) = wordGroup (commutator_rhs 19) := by
  apply word_eq_of_matrix_eq
  exact commutator_19_left.trans commutator_19_right.symm

private def commutator_20_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(1, e1), (2, e1)],
    [(1, e1), (2, e1), (3, e1)],
    [(0, e1), (1, e1), (3, e1), (4, e1)],
    [(5, e1)],
    [(1, e1), (6, e1)],
    [(5, e1), (7, e1)],
    [(8, e1)],
    [(1, e1), (5, e1), (7, e1), (9, e1)],
    [(8, e1), (10, e1)],
    [(1, e1), (2, e1), (5, e1), (9, e1), (11, e1)],
    [(5, e1), (12, e1)],
    [(10, e1), (13, e1)],
    [(14, e1)],
    [(5, e1), (7, e1), (8, e1), (10, e1), (12, e1), (15, e1)],
    [(8, e1), (14, e1), (16, e1)],
    [(1, e1), (5, e1), (6, e1), (7, e1), (8, e1), (9, e1), (12, e1), (15, e1), (17, e1)],
    [(8, e1), (10, e1), (14, e1), (16, e1), (18, e1)],
    [(8, e1), (19, e1)],
    [(5, e1), (10, e1), (13, e1), (14, e1), (18, e1), (20, e1)],
    [(21, e1)],
    [(21, e1), (22, e1)],
    [(14, e1), (21, e1), (22, e1), (23, e1)],
    [(8, e1), (14, e1), (16, e1), (19, e1), (21, e1), (23, e1), (24, e1)],
    [(21, e1), (25, e1)]])
private theorem commutator_20_left_s1 : wordMatrix [Atom.root 5 1] = atomMatrix (Atom.root 5 1) := by simp
private theorem commutator_20_left_s0 : wordMatrix [Atom.root 1 1, Atom.root 5 1] = commutator_20_target := by
  rw [wordMatrix_cons, commutator_20_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 1 1))
  decide +kernel
private theorem commutator_20_left : wordMatrix [Atom.root 1 1, Atom.root 5 1] = commutator_20_target := commutator_20_left_s0
private theorem commutator_20_right_s1 : wordMatrix [Atom.root 1 1] = atomMatrix (Atom.root 1 1) := by simp
private theorem commutator_20_right_s0 : wordMatrix [Atom.root 5 1, Atom.root 1 1] = commutator_20_target := by
  rw [wordMatrix_cons, commutator_20_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 5 1))
  decide +kernel
private theorem commutator_20_right : wordMatrix [Atom.root 5 1, Atom.root 1 1] = commutator_20_target := commutator_20_right_s0
theorem commutator_20 : wordGroup (commutator_lhs 20) = wordGroup (commutator_rhs 20) := by
  apply word_eq_of_matrix_eq
  exact commutator_20_left.trans commutator_20_right.symm

private def commutator_21_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(1, e1), (2, e1)],
    [(1, e1), (2, e1), (3, e1)],
    [(1, e1), (3, e1), (4, e1)],
    [(1, e1), (5, e1)],
    [(0, e1), (6, e1)],
    [(1, e1), (2, e1), (5, e1), (7, e1)],
    [(8, e1)],
    [(1, e1), (2, e1), (3, e1), (5, e1), (7, e1), (9, e1)],
    [(8, e1), (10, e1)],
    [(1, e1), (3, e1), (4, e1), (5, e1), (9, e1), (11, e1)],
    [(12, e1)],
    [(6, e1), (10, e1), (13, e1)],
    [(1, e1), (5, e1), (14, e1)],
    [(8, e1), (10, e1), (12, e1), (15, e1)],
    [(1, e1), (2, e1), (5, e1), (7, e1), (14, e1), (16, e1)],
    [(8, e1), (12, e1), (15, e1), (17, e1)],
    [(1, e1), (2, e1), (3, e1), (5, e1), (7, e1), (9, e1), (14, e1), (16, e1), (18, e1)],
    [(0, e1), (6, e1), (12, e1), (19, e1)],
    [(1, e1), (3, e1), (4, e1), (5, e1), (9, e1), (11, e1), (14, e1), (18, e1), (20, e1)],
    [(1, e1), (14, e1), (21, e1)],
    [(1, e1), (2, e1), (14, e1), (16, e1), (21, e1), (22, e1)],
    [(1, e1), (2, e1), (3, e1), (14, e1), (16, e1), (18, e1), (21, e1), (22, e1), (23, e1)],
    [(1, e1), (3, e1), (4, e1), (14, e1), (18, e1), (20, e1), (21, e1), (23, e1), (24, e1)],
    [(0, e1), (12, e1), (19, e1), (25, e1)]])
private theorem commutator_21_left_s1 : wordMatrix [Atom.root 6 1] = atomMatrix (Atom.root 6 1) := by simp
private theorem commutator_21_left_s0 : wordMatrix [Atom.root 1 1, Atom.root 6 1] = commutator_21_target := by
  rw [wordMatrix_cons, commutator_21_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 1 1))
  decide +kernel
private theorem commutator_21_left : wordMatrix [Atom.root 1 1, Atom.root 6 1] = commutator_21_target := commutator_21_left_s0
private theorem commutator_21_right_s1 : wordMatrix [Atom.root 1 1] = atomMatrix (Atom.root 1 1) := by simp
private theorem commutator_21_right_s0 : wordMatrix [Atom.root 6 1, Atom.root 1 1] = commutator_21_target := by
  rw [wordMatrix_cons, commutator_21_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 6 1))
  decide +kernel
private theorem commutator_21_right : wordMatrix [Atom.root 6 1, Atom.root 1 1] = commutator_21_target := commutator_21_right_s0
theorem commutator_21 : wordGroup (commutator_lhs 21) = wordGroup (commutator_rhs 21) := by
  apply word_eq_of_matrix_eq
  exact commutator_21_left.trans commutator_21_right.symm

private def commutator_22_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(1, e1), (2, e1)],
    [(1, e1), (2, e1), (3, e1)],
    [(1, e1), (3, e1), (4, e1)],
    [(0, e1), (5, e1)],
    [(6, e1)],
    [(0, e1), (5, e1), (7, e1)],
    [(0, e1), (2, e1), (8, e1)],
    [(0, e1), (5, e1), (7, e1), (9, e1)],
    [(0, e1), (2, e1), (3, e1), (8, e1), (10, e1)],
    [(0, e1), (5, e1), (9, e1), (11, e1)],
    [(4, e1), (12, e1)],
    [(3, e1), (4, e1), (10, e1), (13, e1)],
    [(3, e1), (6, e1), (14, e1)],
    [(0, e1), (2, e1), (3, e1), (4, e1), (8, e1), (10, e1), (12, e1), (15, e1)],
    [(3, e1), (4, e1), (6, e1), (14, e1), (16, e1)],
    [(0, e1), (2, e1), (4, e1), (8, e1), (12, e1), (15, e1), (17, e1)],
    [(3, e1), (4, e1), (6, e1), (14, e1), (16, e1), (18, e1)],
    [(11, e1), (19, e1)],
    [(3, e1), (6, e1), (14, e1), (18, e1), (20, e1)],
    [(4, e1), (9, e1), (12, e1), (13, e1), (21, e1)],
    [(4, e1), (9, e1), (11, e1), (12, e1), (13, e1), (15, e1), (21, e1), (22, e1)],
    [(4, e1), (9, e1), (11, e1), (12, e1), (13, e1), (15, e1), (17, e1), (21, e1), (22, e1), (23, e1)],
    [(4, e1), (9, e1), (12, e1), (13, e1), (17, e1), (21, e1), (23, e1), (24, e1)],
    [(17, e1), (20, e1), (25, e1)]])
private theorem commutator_22_left_s1 : wordMatrix [Atom.root 7 1] = atomMatrix (Atom.root 7 1) := by simp
private theorem commutator_22_left_s0 : wordMatrix [Atom.root 1 1, Atom.root 7 1] = commutator_22_target := by
  rw [wordMatrix_cons, commutator_22_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 1 1))
  decide +kernel
private theorem commutator_22_left : wordMatrix [Atom.root 1 1, Atom.root 7 1] = commutator_22_target := commutator_22_left_s0
private theorem commutator_22_right_s4 : wordMatrix [Atom.root 11 1] = atomMatrix (Atom.root 11 1) := by simp
private def commutator_22_right_m3 : Mat := Sparse.eval (![[(0, e1)],
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
private theorem commutator_22_right_s3 : wordMatrix [Atom.root 10 1, Atom.root 11 1] = commutator_22_right_m3 := by
  rw [wordMatrix_cons, commutator_22_right_s4]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 10 1))
  decide +kernel
private def commutator_22_right_m2 : Mat := Sparse.eval (![[(0, e1)],
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
    [(0, e1), (11, e1)],
    [(1, e1), (3, e1), (12, e1)],
    [(0, e1), (1, e1), (13, e1)],
    [(1, e1), (2, e1), (14, e1)],
    [(2, e1), (4, e1), (15, e1)],
    [(2, e1), (6, e1), (16, e1)],
    [(0, e1), (3, e1), (17, e1)],
    [(1, e1), (3, e1), (4, e1), (18, e1)],
    [(0, e1), (5, e1), (9, e1), (19, e1)],
    [(2, e1), (4, e1), (6, e1), (20, e1)],
    [(0, e1), (1, e1), (5, e1), (7, e1), (10, e1), (21, e1)],
    [(0, e1), (1, e1), (2, e1), (3, e1), (7, e1), (8, e1), (13, e1), (22, e1)],
    [(0, e1), (3, e1), (5, e1), (9, e1), (10, e1), (11, e1), (23, e1)],
    [(1, e1), (3, e1), (4, e1), (7, e1), (11, e1), (12, e1), (13, e1), (17, e1), (24, e1)],
    [(0, e1), (2, e1), (3, e1), (4, e1), (6, e1), (8, e1), (12, e1), (14, e1), (15, e1), (18, e1), (25, e1)]])
private theorem commutator_22_right_s2 : wordMatrix [Atom.root 8 1, Atom.root 10 1, Atom.root 11 1] = commutator_22_right_m2 := by
  rw [wordMatrix_cons, commutator_22_right_s3]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 8 1))
  decide +kernel
private def commutator_22_right_m1 : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(1, e1), (2, e1)],
    [(1, e1), (2, e1), (3, e1)],
    [(1, e1), (3, e1), (4, e1)],
    [(5, e1)],
    [(6, e1)],
    [(0, e1), (5, e1), (7, e1)],
    [(1, e1), (8, e1)],
    [(0, e1), (5, e1), (7, e1), (9, e1)],
    [(0, e1), (1, e1), (8, e1), (10, e1)],
    [(0, e1), (5, e1), (9, e1), (11, e1)],
    [(1, e1), (3, e1), (12, e1)],
    [(1, e1), (10, e1), (13, e1)],
    [(1, e1), (2, e1), (14, e1)],
    [(0, e1), (2, e1), (3, e1), (4, e1), (8, e1), (10, e1), (12, e1), (15, e1)],
    [(1, e1), (6, e1), (14, e1), (16, e1)],
    [(0, e1), (2, e1), (4, e1), (8, e1), (12, e1), (15, e1), (17, e1)],
    [(3, e1), (4, e1), (6, e1), (14, e1), (16, e1), (18, e1)],
    [(0, e1), (5, e1), (9, e1), (19, e1)],
    [(3, e1), (6, e1), (14, e1), (18, e1), (20, e1)],
    [(0, e1), (1, e1), (5, e1), (7, e1), (10, e1), (21, e1)],
    [(2, e1), (3, e1), (5, e1), (8, e1), (10, e1), (13, e1), (21, e1), (22, e1)],
    [(0, e1), (2, e1), (8, e1), (9, e1), (11, e1), (13, e1), (21, e1), (22, e1), (23, e1)],
    [(4, e1), (9, e1), (12, e1), (13, e1), (17, e1), (21, e1), (23, e1), (24, e1)],
    [(0, e1), (2, e1), (3, e1), (4, e1), (6, e1), (8, e1), (12, e1), (14, e1), (15, e1), (18, e1), (25, e1)]])
private theorem commutator_22_right_s1 : wordMatrix [Atom.root 1 1, Atom.root 8 1, Atom.root 10 1, Atom.root 11 1] = commutator_22_right_m1 := by
  rw [wordMatrix_cons, commutator_22_right_s2]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 1 1))
  decide +kernel
private theorem commutator_22_right_s0 : wordMatrix [Atom.root 7 1, Atom.root 1 1, Atom.root 8 1, Atom.root 10 1, Atom.root 11 1] = commutator_22_target := by
  rw [wordMatrix_cons, commutator_22_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 7 1))
  decide +kernel
private theorem commutator_22_right : wordMatrix [Atom.root 7 1, Atom.root 1 1, Atom.root 8 1, Atom.root 10 1, Atom.root 11 1] = commutator_22_target := commutator_22_right_s0
theorem commutator_22 : wordGroup (commutator_lhs 22) = wordGroup (commutator_rhs 22) := by
  apply word_eq_of_matrix_eq
  exact commutator_22_left.trans commutator_22_right.symm

private def commutator_23_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(1, e1), (2, e1)],
    [(1, e1), (2, e1), (3, e1)],
    [(1, e1), (3, e1), (4, e1)],
    [(5, e1)],
    [(6, e1)],
    [(0, e1), (5, e1), (7, e1)],
    [(1, e1), (8, e1)],
    [(0, e1), (5, e1), (7, e1), (9, e1)],
    [(0, e1), (1, e1), (8, e1), (10, e1)],
    [(5, e1), (9, e1), (11, e1)],
    [(3, e1), (12, e1)],
    [(0, e1), (10, e1), (13, e1)],
    [(2, e1), (14, e1)],
    [(0, e1), (1, e1), (3, e1), (4, e1), (8, e1), (10, e1), (12, e1), (15, e1)],
    [(2, e1), (6, e1), (14, e1), (16, e1)],
    [(1, e1), (3, e1), (4, e1), (8, e1), (12, e1), (15, e1), (17, e1)],
    [(2, e1), (4, e1), (6, e1), (14, e1), (16, e1), (18, e1)],
    [(9, e1), (19, e1)],
    [(2, e1), (4, e1), (14, e1), (18, e1), (20, e1)],
    [(0, e1), (7, e1), (10, e1), (21, e1)],
    [(0, e1), (3, e1), (7, e1), (10, e1), (13, e1), (21, e1), (22, e1)],
    [(0, e1), (3, e1), (7, e1), (10, e1), (11, e1), (13, e1), (21, e1), (22, e1), (23, e1)],
    [(0, e1), (7, e1), (10, e1), (11, e1), (17, e1), (21, e1), (23, e1), (24, e1)],
    [(4, e1), (15, e1), (18, e1), (25, e1)]])
private theorem commutator_23_left_s1 : wordMatrix [Atom.root 8 1] = atomMatrix (Atom.root 8 1) := by simp
private theorem commutator_23_left_s0 : wordMatrix [Atom.root 1 1, Atom.root 8 1] = commutator_23_target := by
  rw [wordMatrix_cons, commutator_23_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 1 1))
  decide +kernel
private theorem commutator_23_left : wordMatrix [Atom.root 1 1, Atom.root 8 1] = commutator_23_target := commutator_23_left_s0
private theorem commutator_23_right_s4 : wordMatrix [Atom.root 11 1] = atomMatrix (Atom.root 11 1) := by simp
private def commutator_23_right_m3 : Mat := Sparse.eval (![[(0, e1)],
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
private theorem commutator_23_right_s3 : wordMatrix [Atom.root 10 1, Atom.root 11 1] = commutator_23_right_m3 := by
  rw [wordMatrix_cons, commutator_23_right_s4]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 10 1))
  decide +kernel
private def commutator_23_right_m2 : Mat := Sparse.eval (![[(0, e1)],
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
private theorem commutator_23_right_s2 : wordMatrix [Atom.root 9 1, Atom.root 10 1, Atom.root 11 1] = commutator_23_right_m2 := by
  rw [wordMatrix_cons, commutator_23_right_s3]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 9 1))
  decide +kernel
private def commutator_23_right_m1 : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(1, e1), (2, e1)],
    [(1, e1), (2, e1), (3, e1)],
    [(1, e1), (3, e1), (4, e1)],
    [(5, e1)],
    [(6, e1)],
    [(5, e1), (7, e1)],
    [(8, e1)],
    [(0, e1), (5, e1), (7, e1), (9, e1)],
    [(1, e1), (8, e1), (10, e1)],
    [(5, e1), (9, e1), (11, e1)],
    [(1, e1), (2, e1), (12, e1)],
    [(0, e1), (10, e1), (13, e1)],
    [(1, e1), (14, e1)],
    [(0, e1), (8, e1), (10, e1), (12, e1), (15, e1)],
    [(2, e1), (14, e1), (16, e1)],
    [(1, e1), (3, e1), (4, e1), (8, e1), (12, e1), (15, e1), (17, e1)],
    [(1, e1), (2, e1), (3, e1), (6, e1), (14, e1), (16, e1), (18, e1)],
    [(0, e1), (5, e1), (7, e1), (19, e1)],
    [(2, e1), (4, e1), (14, e1), (18, e1), (20, e1)],
    [(1, e1), (5, e1), (8, e1), (21, e1)],
    [(1, e1), (2, e1), (7, e1), (21, e1), (22, e1)],
    [(0, e1), (3, e1), (5, e1), (7, e1), (9, e1), (10, e1), (13, e1), (21, e1), (22, e1), (23, e1)],
    [(0, e1), (1, e1), (3, e1), (4, e1), (7, e1), (8, e1), (10, e1), (11, e1), (12, e1), (15, e1), (21, e1), (23, e1), (24, e1)],
    [(0, e1), (2, e1), (6, e1), (8, e1), (10, e1), (12, e1), (14, e1), (16, e1), (25, e1)]])
private theorem commutator_23_right_s1 : wordMatrix [Atom.root 1 1, Atom.root 9 1, Atom.root 10 1, Atom.root 11 1] = commutator_23_right_m1 := by
  rw [wordMatrix_cons, commutator_23_right_s2]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 1 1))
  decide +kernel
private theorem commutator_23_right_s0 : wordMatrix [Atom.root 8 1, Atom.root 1 1, Atom.root 9 1, Atom.root 10 1, Atom.root 11 1] = commutator_23_target := by
  rw [wordMatrix_cons, commutator_23_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 8 1))
  decide +kernel
private theorem commutator_23_right : wordMatrix [Atom.root 8 1, Atom.root 1 1, Atom.root 9 1, Atom.root 10 1, Atom.root 11 1] = commutator_23_target := commutator_23_right_s0
theorem commutator_23 : wordGroup (commutator_lhs 23) = wordGroup (commutator_rhs 23) := by
  apply word_eq_of_matrix_eq
  exact commutator_23_left.trans commutator_23_right.symm

end Kourovka.Problem2153.WilsonModel.RootData.Relations
