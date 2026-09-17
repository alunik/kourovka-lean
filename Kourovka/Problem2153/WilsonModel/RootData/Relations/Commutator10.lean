import Kourovka.Problem2153.WilsonModel.RootData.Relations.Metadata
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
namespace Kourovka.Problem2153.WilsonModel.RootData.Relations
open Field8 F8
private def commutator_60_target : Mat := Sparse.eval (![[(0, e1)],
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
    [(0, e7), (3, e1), (11, e1)],
    [(1, e6), (7, e1), (12, e1)],
    [(1, e6), (7, e1), (13, e1)],
    [(8, e1), (14, e1)],
    [(2, e7), (6, e1), (15, e1)],
    [(16, e1)],
    [(0, e3), (3, e6), (11, e1), (17, e1)],
    [(1, e5), (7, e1), (12, e1), (13, e1), (18, e1)],
    [(5, e7), (10, e1), (19, e1)],
    [(2, e3), (6, e6), (15, e1), (20, e1)],
    [(21, e1)],
    [(8, e7), (14, e1), (22, e1)],
    [(5, e3), (10, e6), (19, e1), (23, e1)],
    [(1, e7), (7, e4), (12, e7), (13, e7), (18, e1), (24, e1)],
    [(8, e3), (14, e6), (22, e1), (25, e1)]])
private theorem commutator_60_left_s1 : wordMatrix [Atom.root 10 6] = atomMatrix (Atom.root 10 6) := by simp
private theorem commutator_60_left_s0 : wordMatrix [Atom.root 4 1, Atom.root 10 6] = commutator_60_target := by
  rw [wordMatrix_cons, commutator_60_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 4 1))
  decide +kernel
private theorem commutator_60_left : wordMatrix [Atom.root 4 1, Atom.root 10 6] = commutator_60_target := commutator_60_left_s0
private theorem commutator_60_right_s1 : wordMatrix [Atom.root 4 1] = atomMatrix (Atom.root 4 1) := by simp
private theorem commutator_60_right_s0 : wordMatrix [Atom.root 10 6, Atom.root 4 1] = commutator_60_target := by
  rw [wordMatrix_cons, commutator_60_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 10 6))
  decide +kernel
private theorem commutator_60_right : wordMatrix [Atom.root 10 6, Atom.root 4 1] = commutator_60_target := commutator_60_right_s0
theorem commutator_60 : wordGroup (commutator_lhs 60) = wordGroup (commutator_rhs 60) := by
  apply word_eq_of_matrix_eq
  exact commutator_60_left.trans commutator_60_right.symm

private def commutator_61_target : Mat := Sparse.eval (![[(0, e1)],
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
    [(0, e6), (3, e1), (11, e1)],
    [(1, e7), (7, e1), (12, e1)],
    [(1, e7), (7, e1), (13, e1)],
    [(8, e1), (14, e1)],
    [(2, e6), (6, e1), (15, e1)],
    [(16, e1)],
    [(0, e3), (3, e7), (11, e1), (17, e1)],
    [(1, e4), (7, e1), (12, e1), (13, e1), (18, e1)],
    [(5, e6), (10, e1), (19, e1)],
    [(2, e3), (6, e7), (15, e1), (20, e1)],
    [(21, e1)],
    [(8, e6), (14, e1), (22, e1)],
    [(5, e3), (10, e7), (19, e1), (23, e1)],
    [(1, e7), (7, e5), (12, e6), (13, e6), (18, e1), (24, e1)],
    [(8, e3), (14, e7), (22, e1), (25, e1)]])
private theorem commutator_61_left_s1 : wordMatrix [Atom.root 10 7] = atomMatrix (Atom.root 10 7) := by simp
private theorem commutator_61_left_s0 : wordMatrix [Atom.root 4 1, Atom.root 10 7] = commutator_61_target := by
  rw [wordMatrix_cons, commutator_61_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 4 1))
  decide +kernel
private theorem commutator_61_left : wordMatrix [Atom.root 4 1, Atom.root 10 7] = commutator_61_target := commutator_61_left_s0
private theorem commutator_61_right_s1 : wordMatrix [Atom.root 4 1] = atomMatrix (Atom.root 4 1) := by simp
private theorem commutator_61_right_s0 : wordMatrix [Atom.root 10 7, Atom.root 4 1] = commutator_61_target := by
  rw [wordMatrix_cons, commutator_61_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 10 7))
  decide +kernel
private theorem commutator_61_right : wordMatrix [Atom.root 10 7, Atom.root 4 1] = commutator_61_target := commutator_61_right_s0
theorem commutator_61 : wordGroup (commutator_lhs 61) = wordGroup (commutator_rhs 61) := by
  apply word_eq_of_matrix_eq
  exact commutator_61_left.trans commutator_61_right.symm

private def commutator_62_target : Mat := Sparse.eval (![[(0, e1)],
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
    [(0, e1), (3, e1), (11, e1)],
    [(7, e1), (12, e1)],
    [(0, e1), (7, e1), (13, e1)],
    [(1, e1), (8, e1), (14, e1)],
    [(2, e1), (6, e1), (15, e1)],
    [(2, e1), (16, e1)],
    [(0, e1), (11, e1), (17, e1)],
    [(0, e1), (1, e1), (3, e1), (7, e1), (12, e1), (13, e1), (18, e1)],
    [(0, e1), (5, e1), (10, e1), (19, e1)],
    [(2, e1), (4, e1), (15, e1), (20, e1)],
    [(1, e1), (5, e1), (21, e1)],
    [(1, e1), (2, e1), (7, e1), (8, e1), (14, e1), (22, e1)],
    [(0, e1), (3, e1), (5, e1), (9, e1), (19, e1), (23, e1)],
    [(0, e1), (1, e1), (3, e1), (4, e1), (11, e1), (12, e1), (13, e1), (18, e1), (24, e1)],
    [(0, e1), (2, e1), (6, e1), (7, e1), (8, e1), (12, e1), (22, e1), (25, e1)]])
private theorem commutator_62_left_s1 : wordMatrix [Atom.root 11 1] = atomMatrix (Atom.root 11 1) := by simp
private theorem commutator_62_left_s0 : wordMatrix [Atom.root 4 1, Atom.root 11 1] = commutator_62_target := by
  rw [wordMatrix_cons, commutator_62_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 4 1))
  decide +kernel
private theorem commutator_62_left : wordMatrix [Atom.root 4 1, Atom.root 11 1] = commutator_62_target := commutator_62_left_s0
private theorem commutator_62_right_s1 : wordMatrix [Atom.root 4 1] = atomMatrix (Atom.root 4 1) := by simp
private theorem commutator_62_right_s0 : wordMatrix [Atom.root 11 1, Atom.root 4 1] = commutator_62_target := by
  rw [wordMatrix_cons, commutator_62_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 11 1))
  decide +kernel
private theorem commutator_62_right : wordMatrix [Atom.root 11 1, Atom.root 4 1] = commutator_62_target := commutator_62_right_s0
theorem commutator_62 : wordGroup (commutator_lhs 62) = wordGroup (commutator_rhs 62) := by
  apply word_eq_of_matrix_eq
  exact commutator_62_left.trans commutator_62_right.symm

private def commutator_63_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(0, e1), (4, e1)],
    [(1, e1), (5, e1)],
    [(0, e1), (1, e1), (6, e1)],
    [(2, e1), (7, e1)],
    [(8, e1)],
    [(1, e1), (3, e1), (9, e1)],
    [(10, e1)],
    [(2, e1), (4, e1), (11, e1)],
    [(1, e1), (5, e1), (12, e1)],
    [(6, e1), (13, e1)],
    [(1, e1), (5, e1), (14, e1)],
    [(2, e1), (7, e1), (15, e1)],
    [(2, e1), (7, e1), (8, e1), (16, e1)],
    [(0, e1), (1, e1), (3, e1), (6, e1), (9, e1), (17, e1)],
    [(3, e1), (9, e1), (10, e1), (18, e1)],
    [(0, e1), (6, e1), (8, e1), (12, e1), (19, e1)],
    [(1, e1), (4, e1), (5, e1), (6, e1), (11, e1), (13, e1), (20, e1)],
    [(1, e1), (14, e1), (21, e1)],
    [(2, e1), (16, e1), (22, e1)],
    [(1, e1), (3, e1), (5, e1), (14, e1), (18, e1), (23, e1)],
    [(0, e1), (2, e1), (4, e1), (6, e1), (7, e1), (8, e1), (12, e1), (16, e1), (19, e1), (20, e1), (24, e1)],
    [(0, e1), (1, e1), (12, e1), (14, e1), (19, e1), (21, e1), (25, e1)]])
private theorem commutator_63_left_s1 : wordMatrix [Atom.root 6 1] = atomMatrix (Atom.root 6 1) := by simp
private theorem commutator_63_left_s0 : wordMatrix [Atom.root 5 1, Atom.root 6 1] = commutator_63_target := by
  rw [wordMatrix_cons, commutator_63_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 5 1))
  decide +kernel
private theorem commutator_63_left : wordMatrix [Atom.root 5 1, Atom.root 6 1] = commutator_63_target := commutator_63_left_s0
private theorem commutator_63_right_s2 : wordMatrix [Atom.root 10 1] = atomMatrix (Atom.root 10 1) := by simp
private def commutator_63_right_m1 : Mat := Sparse.eval (![[(0, e1)],
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
    [(1, e1), (13, e1)],
    [(14, e1)],
    [(2, e1), (7, e1), (15, e1)],
    [(8, e1), (16, e1)],
    [(0, e1), (1, e1), (3, e1), (6, e1), (9, e1), (17, e1)],
    [(1, e1), (10, e1), (18, e1)],
    [(5, e1), (8, e1), (19, e1)],
    [(1, e1), (2, e1), (5, e1), (6, e1), (13, e1), (20, e1)],
    [(21, e1)],
    [(8, e1), (22, e1)],
    [(5, e1), (10, e1), (14, e1), (23, e1)],
    [(1, e1), (5, e1), (7, e1), (8, e1), (12, e1), (13, e1), (16, e1), (19, e1), (24, e1)],
    [(8, e1), (14, e1), (21, e1), (25, e1)]])
private theorem commutator_63_right_s1 : wordMatrix [Atom.root 5 1, Atom.root 10 1] = commutator_63_right_m1 := by
  rw [wordMatrix_cons, commutator_63_right_s2]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 5 1))
  decide +kernel
private theorem commutator_63_right_s0 : wordMatrix [Atom.root 6 1, Atom.root 5 1, Atom.root 10 1] = commutator_63_target := by
  rw [wordMatrix_cons, commutator_63_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 6 1))
  decide +kernel
private theorem commutator_63_right : wordMatrix [Atom.root 6 1, Atom.root 5 1, Atom.root 10 1] = commutator_63_target := commutator_63_right_s0
theorem commutator_63 : wordGroup (commutator_lhs 63) = wordGroup (commutator_rhs 63) := by
  apply word_eq_of_matrix_eq
  exact commutator_63_left.trans commutator_63_right.symm

private def commutator_64_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(0, e1), (4, e1)],
    [(0, e1), (5, e1)],
    [(1, e1), (6, e1)],
    [(7, e1)],
    [(0, e1), (2, e1), (8, e1)],
    [(1, e1), (9, e1)],
    [(3, e1), (10, e1)],
    [(2, e1), (11, e1)],
    [(0, e1), (4, e1), (5, e1), (12, e1)],
    [(4, e1), (13, e1)],
    [(3, e1), (6, e1), (14, e1)],
    [(7, e1), (15, e1)],
    [(0, e1), (2, e1), (4, e1), (8, e1), (16, e1)],
    [(1, e1), (6, e1), (9, e1), (17, e1)],
    [(3, e1), (10, e1), (18, e1)],
    [(0, e1), (2, e1), (8, e1), (11, e1), (19, e1)],
    [(0, e1), (4, e1), (5, e1), (13, e1), (20, e1)],
    [(4, e1), (9, e1), (12, e1), (13, e1), (21, e1)],
    [(11, e1), (15, e1), (22, e1)],
    [(3, e1), (6, e1), (14, e1), (17, e1), (23, e1)],
    [(0, e1), (2, e1), (4, e1), (8, e1), (11, e1), (16, e1), (19, e1), (24, e1)],
    [(4, e1), (9, e1), (12, e1), (13, e1), (17, e1), (20, e1), (21, e1), (25, e1)]])
private theorem commutator_64_left_s1 : wordMatrix [Atom.root 7 1] = atomMatrix (Atom.root 7 1) := by simp
private theorem commutator_64_left_s0 : wordMatrix [Atom.root 5 1, Atom.root 7 1] = commutator_64_target := by
  rw [wordMatrix_cons, commutator_64_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 5 1))
  decide +kernel
private theorem commutator_64_left : wordMatrix [Atom.root 5 1, Atom.root 7 1] = commutator_64_target := commutator_64_left_s0
private theorem commutator_64_right_s2 : wordMatrix [Atom.root 11 1] = atomMatrix (Atom.root 11 1) := by simp
private def commutator_64_right_m1 : Mat := Sparse.eval (![[(0, e1)],
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
    [(2, e1), (11, e1)],
    [(5, e1), (12, e1)],
    [(0, e1), (13, e1)],
    [(1, e1), (14, e1)],
    [(7, e1), (15, e1)],
    [(2, e1), (8, e1), (16, e1)],
    [(1, e1), (6, e1), (9, e1), (17, e1)],
    [(3, e1), (10, e1), (18, e1)],
    [(0, e1), (8, e1), (19, e1)],
    [(0, e1), (4, e1), (5, e1), (13, e1), (20, e1)],
    [(1, e1), (5, e1), (21, e1)],
    [(2, e1), (7, e1), (22, e1)],
    [(1, e1), (3, e1), (9, e1), (14, e1), (23, e1)],
    [(0, e1), (2, e1), (4, e1), (8, e1), (11, e1), (16, e1), (19, e1), (24, e1)],
    [(0, e1), (1, e1), (5, e1), (6, e1), (12, e1), (21, e1), (25, e1)]])
private theorem commutator_64_right_s1 : wordMatrix [Atom.root 5 1, Atom.root 11 1] = commutator_64_right_m1 := by
  rw [wordMatrix_cons, commutator_64_right_s2]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 5 1))
  decide +kernel
private theorem commutator_64_right_s0 : wordMatrix [Atom.root 7 1, Atom.root 5 1, Atom.root 11 1] = commutator_64_target := by
  rw [wordMatrix_cons, commutator_64_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 7 1))
  decide +kernel
private theorem commutator_64_right : wordMatrix [Atom.root 7 1, Atom.root 5 1, Atom.root 11 1] = commutator_64_target := commutator_64_right_s0
theorem commutator_64 : wordGroup (commutator_lhs 64) = wordGroup (commutator_rhs 64) := by
  apply word_eq_of_matrix_eq
  exact commutator_64_left.trans commutator_64_right.symm

private def commutator_65_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(0, e1), (4, e1)],
    [(5, e1)],
    [(1, e1), (6, e1)],
    [(0, e1), (7, e1)],
    [(1, e1), (8, e1)],
    [(1, e1), (9, e1)],
    [(0, e1), (10, e1)],
    [(2, e1), (11, e1)],
    [(3, e1), (5, e1), (12, e1)],
    [(13, e1)],
    [(2, e1), (14, e1)],
    [(0, e1), (4, e1), (7, e1), (15, e1)],
    [(1, e1), (6, e1), (8, e1), (16, e1)],
    [(1, e1), (6, e1), (9, e1), (17, e1)],
    [(0, e1), (4, e1), (10, e1), (18, e1)],
    [(1, e1), (8, e1), (9, e1), (19, e1)],
    [(5, e1), (13, e1), (20, e1)],
    [(0, e1), (7, e1), (10, e1), (21, e1)],
    [(3, e1), (13, e1), (22, e1)],
    [(2, e1), (11, e1), (14, e1), (23, e1)],
    [(1, e1), (6, e1), (8, e1), (9, e1), (16, e1), (17, e1), (19, e1), (24, e1)],
    [(0, e1), (4, e1), (7, e1), (10, e1), (15, e1), (18, e1), (21, e1), (25, e1)]])
private theorem commutator_65_left_s1 : wordMatrix [Atom.root 8 1] = atomMatrix (Atom.root 8 1) := by simp
private theorem commutator_65_left_s0 : wordMatrix [Atom.root 5 1, Atom.root 8 1] = commutator_65_target := by
  rw [wordMatrix_cons, commutator_65_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 5 1))
  decide +kernel
private theorem commutator_65_left : wordMatrix [Atom.root 5 1, Atom.root 8 1] = commutator_65_target := commutator_65_left_s0
private theorem commutator_65_right_s1 : wordMatrix [Atom.root 5 1] = atomMatrix (Atom.root 5 1) := by simp
private theorem commutator_65_right_s0 : wordMatrix [Atom.root 8 1, Atom.root 5 1] = commutator_65_target := by
  rw [wordMatrix_cons, commutator_65_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 8 1))
  decide +kernel
private theorem commutator_65_right : wordMatrix [Atom.root 8 1, Atom.root 5 1] = commutator_65_target := commutator_65_right_s0
theorem commutator_65 : wordGroup (commutator_lhs 65) = wordGroup (commutator_rhs 65) := by
  apply word_eq_of_matrix_eq
  exact commutator_65_left.trans commutator_65_right.symm

end Kourovka.Problem2153.WilsonModel.RootData.Relations
