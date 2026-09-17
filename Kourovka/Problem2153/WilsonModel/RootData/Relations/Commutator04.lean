import Kourovka.Problem2153.WilsonModel.RootData.Relations.Metadata
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
namespace Kourovka.Problem2153.WilsonModel.RootData.Relations
open Field8 F8
private def commutator_24_target : Mat := Sparse.eval (![[(0, e1)],
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
    [(0, e1), (5, e1), (9, e1), (11, e1)],
    [(2, e1), (12, e1)],
    [(1, e1), (10, e1), (13, e1)],
    [(14, e1)],
    [(0, e1), (1, e1), (2, e1), (8, e1), (10, e1), (12, e1), (15, e1)],
    [(1, e1), (14, e1), (16, e1)],
    [(0, e1), (2, e1), (4, e1), (8, e1), (12, e1), (15, e1), (17, e1)],
    [(1, e1), (6, e1), (14, e1), (16, e1), (18, e1)],
    [(7, e1), (19, e1)],
    [(3, e1), (6, e1), (14, e1), (18, e1), (20, e1)],
    [(8, e1), (21, e1)],
    [(5, e1), (8, e1), (21, e1), (22, e1)],
    [(2, e1), (5, e1), (8, e1), (13, e1), (21, e1), (22, e1), (23, e1)],
    [(0, e1), (2, e1), (8, e1), (9, e1), (13, e1), (15, e1), (21, e1), (23, e1), (24, e1)],
    [(1, e1), (10, e1), (16, e1), (25, e1)]])
private theorem commutator_24_left_s1 : wordMatrix [Atom.root 9 1] = atomMatrix (Atom.root 9 1) := by simp
private theorem commutator_24_left_s0 : wordMatrix [Atom.root 1 1, Atom.root 9 1] = commutator_24_target := by
  rw [wordMatrix_cons, commutator_24_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 1 1))
  decide +kernel
private theorem commutator_24_left : wordMatrix [Atom.root 1 1, Atom.root 9 1] = commutator_24_target := commutator_24_left_s0
private theorem commutator_24_right_s2 : wordMatrix [Atom.root 10 1] = atomMatrix (Atom.root 10 1) := by simp
private def commutator_24_right_m1 : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(1, e1), (2, e1)],
    [(1, e1), (2, e1), (3, e1)],
    [(1, e1), (3, e1), (4, e1)],
    [(5, e1)],
    [(6, e1)],
    [(5, e1), (7, e1)],
    [(8, e1)],
    [(5, e1), (7, e1), (9, e1)],
    [(8, e1), (10, e1)],
    [(0, e1), (5, e1), (9, e1), (11, e1)],
    [(1, e1), (12, e1)],
    [(1, e1), (10, e1), (13, e1)],
    [(14, e1)],
    [(1, e1), (2, e1), (8, e1), (10, e1), (12, e1), (15, e1)],
    [(14, e1), (16, e1)],
    [(0, e1), (1, e1), (2, e1), (3, e1), (8, e1), (12, e1), (15, e1), (17, e1)],
    [(1, e1), (14, e1), (16, e1), (18, e1)],
    [(5, e1), (19, e1)],
    [(1, e1), (2, e1), (6, e1), (14, e1), (18, e1), (20, e1)],
    [(21, e1)],
    [(8, e1), (21, e1), (22, e1)],
    [(5, e1), (8, e1), (10, e1), (21, e1), (22, e1), (23, e1)],
    [(1, e1), (5, e1), (7, e1), (10, e1), (12, e1), (13, e1), (21, e1), (23, e1), (24, e1)],
    [(8, e1), (14, e1), (25, e1)]])
private theorem commutator_24_right_s1 : wordMatrix [Atom.root 1 1, Atom.root 10 1] = commutator_24_right_m1 := by
  rw [wordMatrix_cons, commutator_24_right_s2]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 1 1))
  decide +kernel
private theorem commutator_24_right_s0 : wordMatrix [Atom.root 9 1, Atom.root 1 1, Atom.root 10 1] = commutator_24_target := by
  rw [wordMatrix_cons, commutator_24_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 9 1))
  decide +kernel
private theorem commutator_24_right : wordMatrix [Atom.root 9 1, Atom.root 1 1, Atom.root 10 1] = commutator_24_target := commutator_24_right_s0
theorem commutator_24 : wordGroup (commutator_lhs 24) = wordGroup (commutator_rhs 24) := by
  apply word_eq_of_matrix_eq
  exact commutator_24_left.trans commutator_24_right.symm

private def commutator_25_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(1, e1), (2, e1)],
    [(1, e1), (2, e1), (3, e1)],
    [(1, e1), (3, e1), (4, e1)],
    [(5, e1)],
    [(6, e1)],
    [(5, e1), (7, e1)],
    [(8, e1)],
    [(5, e1), (7, e1), (9, e1)],
    [(8, e1), (10, e1)],
    [(0, e1), (5, e1), (9, e1), (11, e1)],
    [(1, e1), (12, e1)],
    [(1, e1), (10, e1), (13, e1)],
    [(14, e1)],
    [(1, e1), (2, e1), (8, e1), (10, e1), (12, e1), (15, e1)],
    [(14, e1), (16, e1)],
    [(0, e1), (1, e1), (2, e1), (3, e1), (8, e1), (12, e1), (15, e1), (17, e1)],
    [(1, e1), (14, e1), (16, e1), (18, e1)],
    [(5, e1), (19, e1)],
    [(1, e1), (2, e1), (6, e1), (14, e1), (18, e1), (20, e1)],
    [(21, e1)],
    [(8, e1), (21, e1), (22, e1)],
    [(5, e1), (8, e1), (10, e1), (21, e1), (22, e1), (23, e1)],
    [(1, e1), (5, e1), (7, e1), (10, e1), (12, e1), (13, e1), (21, e1), (23, e1), (24, e1)],
    [(8, e1), (14, e1), (25, e1)]])
private theorem commutator_25_left_s1 : wordMatrix [Atom.root 10 1] = atomMatrix (Atom.root 10 1) := by simp
private theorem commutator_25_left_s0 : wordMatrix [Atom.root 1 1, Atom.root 10 1] = commutator_25_target := by
  rw [wordMatrix_cons, commutator_25_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 1 1))
  decide +kernel
private theorem commutator_25_left : wordMatrix [Atom.root 1 1, Atom.root 10 1] = commutator_25_target := commutator_25_left_s0
private theorem commutator_25_right_s1 : wordMatrix [Atom.root 1 1] = atomMatrix (Atom.root 1 1) := by simp
private theorem commutator_25_right_s0 : wordMatrix [Atom.root 10 1, Atom.root 1 1] = commutator_25_target := by
  rw [wordMatrix_cons, commutator_25_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 10 1))
  decide +kernel
private theorem commutator_25_right : wordMatrix [Atom.root 10 1, Atom.root 1 1] = commutator_25_target := commutator_25_right_s0
theorem commutator_25 : wordGroup (commutator_lhs 25) = wordGroup (commutator_rhs 25) := by
  apply word_eq_of_matrix_eq
  exact commutator_25_left.trans commutator_25_right.symm

private def commutator_26_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(1, e1), (2, e1)],
    [(1, e1), (2, e1), (3, e1)],
    [(1, e1), (3, e1), (4, e1)],
    [(5, e1)],
    [(6, e1)],
    [(5, e1), (7, e1)],
    [(8, e1)],
    [(5, e1), (7, e1), (9, e1)],
    [(8, e1), (10, e1)],
    [(5, e1), (9, e1), (11, e1)],
    [(12, e1)],
    [(0, e1), (10, e1), (13, e1)],
    [(1, e1), (14, e1)],
    [(8, e1), (10, e1), (12, e1), (15, e1)],
    [(1, e1), (2, e1), (14, e1), (16, e1)],
    [(8, e1), (12, e1), (15, e1), (17, e1)],
    [(1, e1), (2, e1), (3, e1), (14, e1), (16, e1), (18, e1)],
    [(0, e1), (19, e1)],
    [(1, e1), (3, e1), (4, e1), (14, e1), (18, e1), (20, e1)],
    [(1, e1), (5, e1), (21, e1)],
    [(1, e1), (2, e1), (5, e1), (7, e1), (21, e1), (22, e1)],
    [(1, e1), (2, e1), (3, e1), (5, e1), (7, e1), (9, e1), (21, e1), (22, e1), (23, e1)],
    [(1, e1), (3, e1), (4, e1), (5, e1), (9, e1), (11, e1), (21, e1), (23, e1), (24, e1)],
    [(0, e1), (6, e1), (12, e1), (25, e1)]])
private theorem commutator_26_left_s1 : wordMatrix [Atom.root 11 1] = atomMatrix (Atom.root 11 1) := by simp
private theorem commutator_26_left_s0 : wordMatrix [Atom.root 1 1, Atom.root 11 1] = commutator_26_target := by
  rw [wordMatrix_cons, commutator_26_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 1 1))
  decide +kernel
private theorem commutator_26_left : wordMatrix [Atom.root 1 1, Atom.root 11 1] = commutator_26_target := commutator_26_left_s0
private theorem commutator_26_right_s1 : wordMatrix [Atom.root 1 1] = atomMatrix (Atom.root 1 1) := by simp
private theorem commutator_26_right_s0 : wordMatrix [Atom.root 11 1, Atom.root 1 1] = commutator_26_target := by
  rw [wordMatrix_cons, commutator_26_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 11 1))
  decide +kernel
private theorem commutator_26_right : wordMatrix [Atom.root 11 1, Atom.root 1 1] = commutator_26_target := commutator_26_right_s0
theorem commutator_26 : wordGroup (commutator_lhs 26) = wordGroup (commutator_rhs 26) := by
  apply word_eq_of_matrix_eq
  exact commutator_26_left.trans commutator_26_right.symm

private def commutator_27_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(0, e1), (2, e1)],
    [(1, e1), (3, e1)],
    [(1, e1), (2, e1), (4, e1)],
    [(0, e1), (2, e1), (5, e1)],
    [(1, e1), (3, e1), (6, e1)],
    [(7, e1)],
    [(0, e1), (5, e1), (8, e1)],
    [(1, e1), (2, e1), (4, e1), (5, e1), (9, e1)],
    [(1, e1), (3, e1), (6, e1), (10, e1)],
    [(5, e1), (7, e1), (11, e1)],
    [(5, e1), (9, e1), (12, e1)],
    [(5, e1), (8, e1), (9, e1), (13, e1)],
    [(1, e1), (3, e1), (10, e1), (14, e1)],
    [(5, e1), (7, e1), (8, e1), (11, e1), (15, e1)],
    [(1, e1), (2, e1), (4, e1), (5, e1), (8, e1), (9, e1), (12, e1), (13, e1), (16, e1)],
    [(8, e1), (10, e1), (12, e1), (17, e1)],
    [(14, e1), (18, e1)],
    [(5, e1), (7, e1), (8, e1), (11, e1), (15, e1), (19, e1)],
    [(8, e1), (10, e1), (12, e1), (14, e1), (16, e1), (17, e1), (20, e1)],
    [(1, e1), (2, e1), (4, e1), (8, e1), (12, e1), (13, e1), (16, e1), (21, e1)],
    [(5, e1), (7, e1), (11, e1), (19, e1), (22, e1)],
    [(8, e1), (10, e1), (12, e1), (14, e1), (16, e1), (17, e1), (20, e1), (21, e1), (23, e1)],
    [(21, e1), (22, e1), (24, e1)],
    [(8, e1), (10, e1), (12, e1), (17, e1), (21, e1), (23, e1), (25, e1)]])
private theorem commutator_27_left_s1 : wordMatrix [Atom.root 3 1] = atomMatrix (Atom.root 3 1) := by simp
private theorem commutator_27_left_s0 : wordMatrix [Atom.root 2 1, Atom.root 3 1] = commutator_27_target := by
  rw [wordMatrix_cons, commutator_27_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 2 1))
  decide +kernel
private theorem commutator_27_left : wordMatrix [Atom.root 2 1, Atom.root 3 1] = commutator_27_target := commutator_27_left_s0
private theorem commutator_27_right_s4 : wordMatrix [Atom.root 11 1] = atomMatrix (Atom.root 11 1) := by simp
private def commutator_27_right_m3 : Mat := Sparse.eval (![[(0, e1)],
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
private theorem commutator_27_right_s3 : wordMatrix [Atom.root 10 1, Atom.root 11 1] = commutator_27_right_m3 := by
  rw [wordMatrix_cons, commutator_27_right_s4]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 10 1))
  decide +kernel
private def commutator_27_right_m2 : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(0, e1), (4, e1)],
    [(5, e1)],
    [(1, e1), (6, e1)],
    [(7, e1)],
    [(8, e1)],
    [(1, e1), (9, e1)],
    [(10, e1)],
    [(0, e1), (2, e1), (11, e1)],
    [(1, e1), (5, e1), (12, e1)],
    [(0, e1), (1, e1), (13, e1)],
    [(1, e1), (14, e1)],
    [(2, e1), (7, e1), (15, e1)],
    [(2, e1), (8, e1), (16, e1)],
    [(0, e1), (1, e1), (3, e1), (6, e1), (9, e1), (17, e1)],
    [(1, e1), (3, e1), (10, e1), (18, e1)],
    [(0, e1), (5, e1), (8, e1), (19, e1)],
    [(0, e1), (1, e1), (2, e1), (4, e1), (5, e1), (6, e1), (13, e1), (20, e1)],
    [(1, e1), (5, e1), (21, e1)],
    [(2, e1), (7, e1), (8, e1), (22, e1)],
    [(1, e1), (3, e1), (5, e1), (9, e1), (10, e1), (14, e1), (23, e1)],
    [(1, e1), (2, e1), (4, e1), (5, e1), (7, e1), (8, e1), (11, e1), (12, e1), (13, e1), (16, e1), (19, e1), (24, e1)],
    [(0, e1), (5, e1), (6, e1), (8, e1), (12, e1), (14, e1), (21, e1), (25, e1)]])
private theorem commutator_27_right_s2 : wordMatrix [Atom.root 5 1, Atom.root 10 1, Atom.root 11 1] = commutator_27_right_m2 := by
  rw [wordMatrix_cons, commutator_27_right_s3]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 5 1))
  decide +kernel
private def commutator_27_right_m1 : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(0, e1), (2, e1)],
    [(3, e1)],
    [(0, e1), (4, e1)],
    [(0, e1), (2, e1), (5, e1)],
    [(1, e1), (3, e1), (6, e1)],
    [(7, e1)],
    [(0, e1), (5, e1), (8, e1)],
    [(0, e1), (1, e1), (4, e1), (9, e1)],
    [(1, e1), (3, e1), (6, e1), (10, e1)],
    [(0, e1), (2, e1), (11, e1)],
    [(5, e1), (9, e1), (12, e1)],
    [(0, e1), (9, e1), (13, e1)],
    [(1, e1), (3, e1), (10, e1), (14, e1)],
    [(0, e1), (7, e1), (11, e1), (15, e1)],
    [(1, e1), (2, e1), (4, e1), (5, e1), (8, e1), (9, e1), (12, e1), (13, e1), (16, e1)],
    [(0, e1), (1, e1), (3, e1), (6, e1), (9, e1), (17, e1)],
    [(1, e1), (3, e1), (10, e1), (18, e1)],
    [(5, e1), (7, e1), (8, e1), (11, e1), (15, e1), (19, e1)],
    [(2, e1), (3, e1), (4, e1), (5, e1), (9, e1), (13, e1), (17, e1), (20, e1)],
    [(1, e1), (2, e1), (4, e1), (8, e1), (12, e1), (13, e1), (16, e1), (21, e1)],
    [(5, e1), (7, e1), (11, e1), (19, e1), (22, e1)],
    [(1, e1), (2, e1), (4, e1), (10, e1), (13, e1), (14, e1), (17, e1), (20, e1), (23, e1)],
    [(1, e1), (2, e1), (4, e1), (5, e1), (7, e1), (8, e1), (11, e1), (12, e1), (13, e1), (16, e1), (19, e1), (24, e1)],
    [(8, e1), (10, e1), (12, e1), (17, e1), (21, e1), (23, e1), (25, e1)]])
private theorem commutator_27_right_s1 : wordMatrix [Atom.root 2 1, Atom.root 5 1, Atom.root 10 1, Atom.root 11 1] = commutator_27_right_m1 := by
  rw [wordMatrix_cons, commutator_27_right_s2]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 2 1))
  decide +kernel
private theorem commutator_27_right_s0 : wordMatrix [Atom.root 3 1, Atom.root 2 1, Atom.root 5 1, Atom.root 10 1, Atom.root 11 1] = commutator_27_target := by
  rw [wordMatrix_cons, commutator_27_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 3 1))
  decide +kernel
private theorem commutator_27_right : wordMatrix [Atom.root 3 1, Atom.root 2 1, Atom.root 5 1, Atom.root 10 1, Atom.root 11 1] = commutator_27_target := commutator_27_right_s0
theorem commutator_27 : wordGroup (commutator_lhs 27) = wordGroup (commutator_rhs 27) := by
  apply word_eq_of_matrix_eq
  exact commutator_27_left.trans commutator_27_right.symm

private def commutator_28_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(0, e1), (2, e1)],
    [(0, e1), (3, e1)],
    [(4, e1)],
    [(0, e1), (2, e1), (5, e1)],
    [(0, e1), (2, e1), (3, e1), (6, e1)],
    [(1, e1), (7, e1)],
    [(0, e1), (5, e1), (8, e1)],
    [(4, e1), (9, e1)],
    [(0, e1), (2, e1), (3, e1), (5, e1), (6, e1), (10, e1)],
    [(0, e1), (3, e1), (11, e1)],
    [(7, e1), (9, e1), (12, e1)],
    [(7, e1), (9, e1), (13, e1)],
    [(0, e1), (3, e1), (5, e1), (8, e1), (10, e1), (14, e1)],
    [(0, e1), (2, e1), (3, e1), (6, e1), (11, e1), (15, e1)],
    [(4, e1), (9, e1), (12, e1), (13, e1), (16, e1)],
    [(0, e1), (11, e1), (17, e1)],
    [(1, e1), (7, e1), (12, e1), (13, e1), (18, e1)],
    [(0, e1), (2, e1), (3, e1), (5, e1), (6, e1), (10, e1), (11, e1), (15, e1), (19, e1)],
    [(0, e1), (2, e1), (11, e1), (15, e1), (17, e1), (20, e1)],
    [(4, e1), (12, e1), (13, e1), (16, e1), (21, e1)],
    [(0, e1), (3, e1), (5, e1), (8, e1), (10, e1), (11, e1), (14, e1), (19, e1), (22, e1)],
    [(0, e1), (2, e1), (5, e1), (11, e1), (15, e1), (17, e1), (19, e1), (20, e1), (23, e1)],
    [(1, e1), (12, e1), (13, e1), (18, e1), (24, e1)],
    [(0, e1), (5, e1), (8, e1), (11, e1), (17, e1), (19, e1), (22, e1), (23, e1), (25, e1)]])
private theorem commutator_28_left_s1 : wordMatrix [Atom.root 4 1] = atomMatrix (Atom.root 4 1) := by simp
private theorem commutator_28_left_s0 : wordMatrix [Atom.root 2 1, Atom.root 4 1] = commutator_28_target := by
  rw [wordMatrix_cons, commutator_28_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 2 1))
  decide +kernel
private theorem commutator_28_left : wordMatrix [Atom.root 2 1, Atom.root 4 1] = commutator_28_target := commutator_28_left_s0
private theorem commutator_28_right_s1 : wordMatrix [Atom.root 2 1] = atomMatrix (Atom.root 2 1) := by simp
private theorem commutator_28_right_s0 : wordMatrix [Atom.root 4 1, Atom.root 2 1] = commutator_28_target := by
  rw [wordMatrix_cons, commutator_28_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 4 1))
  decide +kernel
private theorem commutator_28_right : wordMatrix [Atom.root 4 1, Atom.root 2 1] = commutator_28_target := commutator_28_right_s0
theorem commutator_28 : wordGroup (commutator_lhs 28) = wordGroup (commutator_rhs 28) := by
  apply word_eq_of_matrix_eq
  exact commutator_28_left.trans commutator_28_right.symm

private def commutator_29_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(0, e1), (2, e1)],
    [(3, e1)],
    [(0, e1), (4, e1)],
    [(0, e1), (2, e1), (5, e1)],
    [(1, e1), (3, e1), (6, e1)],
    [(7, e1)],
    [(0, e1), (5, e1), (8, e1)],
    [(0, e1), (1, e1), (4, e1), (9, e1)],
    [(1, e1), (3, e1), (6, e1), (10, e1)],
    [(2, e1), (11, e1)],
    [(1, e1), (5, e1), (9, e1), (12, e1)],
    [(1, e1), (9, e1), (13, e1)],
    [(3, e1), (10, e1), (14, e1)],
    [(2, e1), (7, e1), (11, e1), (15, e1)],
    [(0, e1), (1, e1), (4, e1), (5, e1), (8, e1), (9, e1), (12, e1), (13, e1), (16, e1)],
    [(1, e1), (6, e1), (9, e1), (17, e1)],
    [(10, e1), (18, e1)],
    [(2, e1), (7, e1), (8, e1), (11, e1), (15, e1), (19, e1)],
    [(1, e1), (5, e1), (6, e1), (9, e1), (13, e1), (17, e1), (20, e1)],
    [(0, e1), (4, e1), (5, e1), (8, e1), (12, e1), (13, e1), (16, e1), (21, e1)],
    [(2, e1), (8, e1), (11, e1), (19, e1), (22, e1)],
    [(1, e1), (5, e1), (6, e1), (9, e1), (13, e1), (14, e1), (17, e1), (20, e1), (23, e1)],
    [(8, e1), (16, e1), (19, e1), (24, e1)],
    [(1, e1), (6, e1), (9, e1), (14, e1), (17, e1), (21, e1), (23, e1), (25, e1)]])
private theorem commutator_29_left_s1 : wordMatrix [Atom.root 5 1] = atomMatrix (Atom.root 5 1) := by simp
private theorem commutator_29_left_s0 : wordMatrix [Atom.root 2 1, Atom.root 5 1] = commutator_29_target := by
  rw [wordMatrix_cons, commutator_29_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 2 1))
  decide +kernel
private theorem commutator_29_left : wordMatrix [Atom.root 2 1, Atom.root 5 1] = commutator_29_target := commutator_29_left_s0
private theorem commutator_29_right_s4 : wordMatrix [Atom.root 11 1] = atomMatrix (Atom.root 11 1) := by simp
private def commutator_29_right_m3 : Mat := Sparse.eval (![[(0, e1)],
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
private theorem commutator_29_right_s3 : wordMatrix [Atom.root 10 1, Atom.root 11 1] = commutator_29_right_m3 := by
  rw [wordMatrix_cons, commutator_29_right_s4]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 10 1))
  decide +kernel
private def commutator_29_right_m2 : Mat := Sparse.eval (![[(0, e1)],
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
private theorem commutator_29_right_s2 : wordMatrix [Atom.root 9 1, Atom.root 10 1, Atom.root 11 1] = commutator_29_right_m2 := by
  rw [wordMatrix_cons, commutator_29_right_s3]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 9 1))
  decide +kernel
private def commutator_29_right_m1 : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(0, e1), (2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(0, e1), (2, e1), (5, e1)],
    [(3, e1), (6, e1)],
    [(7, e1)],
    [(0, e1), (5, e1), (8, e1)],
    [(0, e1), (4, e1), (9, e1)],
    [(1, e1), (3, e1), (6, e1), (10, e1)],
    [(0, e1), (11, e1)],
    [(0, e1), (1, e1), (2, e1), (9, e1), (12, e1)],
    [(1, e1), (9, e1), (13, e1)],
    [(3, e1), (10, e1), (14, e1)],
    [(2, e1), (11, e1), (15, e1)],
    [(1, e1), (4, e1), (9, e1), (12, e1), (13, e1), (16, e1)],
    [(0, e1), (3, e1), (4, e1), (17, e1)],
    [(1, e1), (3, e1), (6, e1), (18, e1)],
    [(0, e1), (2, e1), (5, e1), (7, e1), (11, e1), (15, e1), (19, e1)],
    [(0, e1), (2, e1), (6, e1), (17, e1), (20, e1)],
    [(0, e1), (4, e1), (5, e1), (8, e1), (12, e1), (13, e1), (16, e1), (21, e1)],
    [(2, e1), (8, e1), (11, e1), (19, e1), (22, e1)],
    [(1, e1), (3, e1), (5, e1), (6, e1), (9, e1), (10, e1), (13, e1), (17, e1), (20, e1), (23, e1)],
    [(1, e1), (2, e1), (4, e1), (7, e1), (9, e1), (11, e1), (12, e1), (13, e1), (15, e1), (24, e1)],
    [(0, e1), (1, e1), (4, e1), (5, e1), (6, e1), (8, e1), (9, e1), (12, e1), (13, e1), (14, e1), (16, e1), (17, e1), (23, e1), (25, e1)]])
private theorem commutator_29_right_s1 : wordMatrix [Atom.root 2 1, Atom.root 9 1, Atom.root 10 1, Atom.root 11 1] = commutator_29_right_m1 := by
  rw [wordMatrix_cons, commutator_29_right_s2]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 2 1))
  decide +kernel
private theorem commutator_29_right_s0 : wordMatrix [Atom.root 5 1, Atom.root 2 1, Atom.root 9 1, Atom.root 10 1, Atom.root 11 1] = commutator_29_target := by
  rw [wordMatrix_cons, commutator_29_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 5 1))
  decide +kernel
private theorem commutator_29_right : wordMatrix [Atom.root 5 1, Atom.root 2 1, Atom.root 9 1, Atom.root 10 1, Atom.root 11 1] = commutator_29_target := commutator_29_right_s0
theorem commutator_29 : wordGroup (commutator_lhs 29) = wordGroup (commutator_rhs 29) := by
  apply word_eq_of_matrix_eq
  exact commutator_29_left.trans commutator_29_right.symm

end Kourovka.Problem2153.WilsonModel.RootData.Relations
