import Kourovka.Problem2153.WilsonModel.RootData.Relations.Metadata
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
namespace Kourovka.Problem2153.WilsonModel.RootData.Relations
open Field8 F8
private def commutator_48_target : Mat := Sparse.eval (![[(0, e1)],
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
private theorem commutator_48_left_s1 : wordMatrix [Atom.root 10 1] = atomMatrix (Atom.root 10 1) := by simp
private theorem commutator_48_left_s0 : wordMatrix [Atom.root 3 1, Atom.root 10 1] = commutator_48_target := by
  rw [wordMatrix_cons, commutator_48_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 3 1))
  decide +kernel
private theorem commutator_48_left : wordMatrix [Atom.root 3 1, Atom.root 10 1] = commutator_48_target := commutator_48_left_s0
private theorem commutator_48_right_s1 : wordMatrix [Atom.root 3 1] = atomMatrix (Atom.root 3 1) := by simp
private theorem commutator_48_right_s0 : wordMatrix [Atom.root 10 1, Atom.root 3 1] = commutator_48_target := by
  rw [wordMatrix_cons, commutator_48_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 10 1))
  decide +kernel
private theorem commutator_48_right : wordMatrix [Atom.root 10 1, Atom.root 3 1] = commutator_48_target := commutator_48_right_s0
theorem commutator_48 : wordGroup (commutator_lhs 48) = wordGroup (commutator_rhs 48) := by
  apply word_eq_of_matrix_eq
  exact commutator_48_left.trans commutator_48_right.symm

private def commutator_49_target : Mat := Sparse.eval (![[(0, e1)],
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
    [(5, e1), (7, e1), (11, e1)],
    [(12, e1)],
    [(0, e1), (8, e1), (13, e1)],
    [(1, e1), (14, e1)],
    [(8, e1), (15, e1)],
    [(2, e1), (16, e1)],
    [(8, e1), (10, e1), (12, e1), (17, e1)],
    [(1, e1), (3, e1), (14, e1), (18, e1)],
    [(0, e1), (19, e1)],
    [(1, e1), (2, e1), (4, e1), (14, e1), (16, e1), (20, e1)],
    [(1, e1), (5, e1), (21, e1)],
    [(2, e1), (7, e1), (22, e1)],
    [(1, e1), (3, e1), (5, e1), (9, e1), (21, e1), (23, e1)],
    [(1, e1), (2, e1), (4, e1), (5, e1), (7, e1), (11, e1), (21, e1), (22, e1), (24, e1)],
    [(0, e1), (6, e1), (12, e1), (25, e1)]])
private theorem commutator_49_left_s1 : wordMatrix [Atom.root 11 1] = atomMatrix (Atom.root 11 1) := by simp
private theorem commutator_49_left_s0 : wordMatrix [Atom.root 3 1, Atom.root 11 1] = commutator_49_target := by
  rw [wordMatrix_cons, commutator_49_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 3 1))
  decide +kernel
private theorem commutator_49_left : wordMatrix [Atom.root 3 1, Atom.root 11 1] = commutator_49_target := commutator_49_left_s0
private theorem commutator_49_right_s1 : wordMatrix [Atom.root 3 1] = atomMatrix (Atom.root 3 1) := by simp
private theorem commutator_49_right_s0 : wordMatrix [Atom.root 11 1, Atom.root 3 1] = commutator_49_target := by
  rw [wordMatrix_cons, commutator_49_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 11 1))
  decide +kernel
private theorem commutator_49_right : wordMatrix [Atom.root 11 1, Atom.root 3 1] = commutator_49_target := commutator_49_right_s0
theorem commutator_49 : wordGroup (commutator_lhs 49) = wordGroup (commutator_rhs 49) := by
  apply word_eq_of_matrix_eq
  exact commutator_49_left.trans commutator_49_right.symm

private def commutator_50_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(0, e1), (3, e1)],
    [(0, e1), (4, e1)],
    [(5, e1)],
    [(1, e1), (2, e1), (6, e1)],
    [(1, e1), (7, e1)],
    [(8, e1)],
    [(1, e1), (9, e1)],
    [(5, e1), (10, e1)],
    [(0, e1), (2, e1), (3, e1), (11, e1)],
    [(5, e1), (7, e1), (12, e1)],
    [(7, e1), (13, e1)],
    [(8, e1), (14, e1)],
    [(1, e1), (2, e1), (6, e1), (7, e1), (15, e1)],
    [(8, e1), (16, e1)],
    [(0, e1), (1, e1), (2, e1), (6, e1), (9, e1), (11, e1), (17, e1)],
    [(1, e1), (5, e1), (7, e1), (10, e1), (12, e1), (13, e1), (18, e1)],
    [(5, e1), (8, e1), (10, e1), (19, e1)],
    [(2, e1), (5, e1), (7, e1), (13, e1), (15, e1), (20, e1)],
    [(21, e1)],
    [(8, e1), (14, e1), (22, e1)],
    [(5, e1), (8, e1), (14, e1), (19, e1), (23, e1)],
    [(1, e1), (5, e1), (8, e1), (10, e1), (12, e1), (13, e1), (16, e1), (18, e1), (19, e1), (24, e1)],
    [(8, e1), (21, e1), (22, e1), (25, e1)]])
private theorem commutator_50_left_s1 : wordMatrix [Atom.root 5 1] = atomMatrix (Atom.root 5 1) := by simp
private theorem commutator_50_left_s0 : wordMatrix [Atom.root 4 1, Atom.root 5 1] = commutator_50_target := by
  rw [wordMatrix_cons, commutator_50_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 4 1))
  decide +kernel
private theorem commutator_50_left : wordMatrix [Atom.root 4 1, Atom.root 5 1] = commutator_50_target := commutator_50_left_s0
private theorem commutator_50_right_s1 : wordMatrix [Atom.root 4 1] = atomMatrix (Atom.root 4 1) := by simp
private theorem commutator_50_right_s0 : wordMatrix [Atom.root 5 1, Atom.root 4 1] = commutator_50_target := by
  rw [wordMatrix_cons, commutator_50_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 5 1))
  decide +kernel
private theorem commutator_50_right : wordMatrix [Atom.root 5 1, Atom.root 4 1] = commutator_50_target := commutator_50_right_s0
theorem commutator_50 : wordGroup (commutator_lhs 50) = wordGroup (commutator_rhs 50) := by
  apply word_eq_of_matrix_eq
  exact commutator_50_left.trans commutator_50_right.symm

private def commutator_51_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(0, e1), (3, e1)],
    [(4, e1)],
    [(1, e1), (5, e1)],
    [(0, e1), (2, e1), (6, e1)],
    [(1, e1), (2, e1), (7, e1)],
    [(8, e1)],
    [(3, e1), (9, e1)],
    [(1, e1), (5, e1), (10, e1)],
    [(0, e1), (3, e1), (4, e1), (11, e1)],
    [(2, e1), (7, e1), (12, e1)],
    [(2, e1), (6, e1), (7, e1), (13, e1)],
    [(1, e1), (5, e1), (8, e1), (14, e1)],
    [(0, e1), (2, e1), (6, e1), (15, e1)],
    [(2, e1), (7, e1), (16, e1)],
    [(0, e1), (4, e1), (11, e1), (17, e1)],
    [(1, e1), (2, e1), (3, e1), (6, e1), (7, e1), (9, e1), (12, e1), (13, e1), (18, e1)],
    [(0, e1), (1, e1), (5, e1), (6, e1), (10, e1), (12, e1), (19, e1)],
    [(2, e1), (4, e1), (11, e1), (15, e1), (20, e1)],
    [(1, e1), (14, e1), (21, e1)],
    [(1, e1), (2, e1), (5, e1), (8, e1), (14, e1), (16, e1), (22, e1)],
    [(0, e1), (1, e1), (3, e1), (5, e1), (6, e1), (12, e1), (18, e1), (19, e1), (23, e1)],
    [(1, e1), (3, e1), (4, e1), (6, e1), (9, e1), (12, e1), (13, e1), (18, e1), (20, e1), (24, e1)],
    [(0, e1), (2, e1), (8, e1), (12, e1), (16, e1), (19, e1), (22, e1), (25, e1)]])
private theorem commutator_51_left_s1 : wordMatrix [Atom.root 6 1] = atomMatrix (Atom.root 6 1) := by simp
private theorem commutator_51_left_s0 : wordMatrix [Atom.root 4 1, Atom.root 6 1] = commutator_51_target := by
  rw [wordMatrix_cons, commutator_51_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 4 1))
  decide +kernel
private theorem commutator_51_left : wordMatrix [Atom.root 4 1, Atom.root 6 1] = commutator_51_target := commutator_51_left_s0
private theorem commutator_51_right_s2 : wordMatrix [Atom.root 9 1] = atomMatrix (Atom.root 9 1) := by simp
private def commutator_51_right_m1 : Mat := Sparse.eval (![[(0, e1)],
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
private theorem commutator_51_right_s1 : wordMatrix [Atom.root 4 1, Atom.root 9 1] = commutator_51_right_m1 := by
  rw [wordMatrix_cons, commutator_51_right_s2]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 4 1))
  decide +kernel
private theorem commutator_51_right_s0 : wordMatrix [Atom.root 6 1, Atom.root 4 1, Atom.root 9 1] = commutator_51_target := by
  rw [wordMatrix_cons, commutator_51_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 6 1))
  decide +kernel
private theorem commutator_51_right : wordMatrix [Atom.root 6 1, Atom.root 4 1, Atom.root 9 1] = commutator_51_target := commutator_51_right_s0
theorem commutator_51 : wordGroup (commutator_lhs 51) = wordGroup (commutator_rhs 51) := by
  apply word_eq_of_matrix_eq
  exact commutator_51_left.trans commutator_51_right.symm

private def commutator_52_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(0, e1), (3, e1)],
    [(4, e1)],
    [(0, e1), (5, e1)],
    [(2, e1), (6, e1)],
    [(1, e1), (7, e1)],
    [(0, e1), (2, e1), (8, e1)],
    [(9, e1)],
    [(0, e1), (3, e1), (5, e1), (10, e1)],
    [(0, e1), (3, e1), (11, e1)],
    [(4, e1), (7, e1), (12, e1)],
    [(4, e1), (7, e1), (13, e1)],
    [(0, e1), (2, e1), (3, e1), (6, e1), (8, e1), (14, e1)],
    [(2, e1), (6, e1), (15, e1)],
    [(4, e1), (16, e1)],
    [(0, e1), (11, e1), (17, e1)],
    [(1, e1), (7, e1), (12, e1), (13, e1), (18, e1)],
    [(0, e1), (3, e1), (5, e1), (10, e1), (11, e1), (19, e1)],
    [(2, e1), (15, e1), (20, e1)],
    [(4, e1), (9, e1), (12, e1), (13, e1), (21, e1)],
    [(0, e1), (2, e1), (3, e1), (6, e1), (8, e1), (11, e1), (14, e1), (15, e1), (22, e1)],
    [(0, e1), (5, e1), (11, e1), (17, e1), (19, e1), (23, e1)],
    [(1, e1), (12, e1), (13, e1), (18, e1), (24, e1)],
    [(0, e1), (2, e1), (8, e1), (11, e1), (15, e1), (17, e1), (20, e1), (22, e1), (25, e1)]])
private theorem commutator_52_left_s1 : wordMatrix [Atom.root 7 1] = atomMatrix (Atom.root 7 1) := by simp
private theorem commutator_52_left_s0 : wordMatrix [Atom.root 4 1, Atom.root 7 1] = commutator_52_target := by
  rw [wordMatrix_cons, commutator_52_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 4 1))
  decide +kernel
private theorem commutator_52_left : wordMatrix [Atom.root 4 1, Atom.root 7 1] = commutator_52_target := commutator_52_left_s0
private theorem commutator_52_right_s1 : wordMatrix [Atom.root 4 1] = atomMatrix (Atom.root 4 1) := by simp
private theorem commutator_52_right_s0 : wordMatrix [Atom.root 7 1, Atom.root 4 1] = commutator_52_target := by
  rw [wordMatrix_cons, commutator_52_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 7 1))
  decide +kernel
private theorem commutator_52_right : wordMatrix [Atom.root 7 1, Atom.root 4 1] = commutator_52_target := commutator_52_right_s0
theorem commutator_52 : wordGroup (commutator_lhs 52) = wordGroup (commutator_rhs 52) := by
  apply word_eq_of_matrix_eq
  exact commutator_52_left.trans commutator_52_right.symm

private def commutator_53_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(0, e1), (3, e1)],
    [(4, e1)],
    [(5, e1)],
    [(2, e1), (6, e1)],
    [(0, e1), (1, e1), (7, e1)],
    [(1, e1), (8, e1)],
    [(9, e1)],
    [(0, e1), (5, e1), (10, e1)],
    [(0, e1), (3, e1), (11, e1)],
    [(0, e1), (3, e1), (7, e1), (12, e1)],
    [(0, e1), (7, e1), (13, e1)],
    [(1, e1), (2, e1), (8, e1), (14, e1)],
    [(2, e1), (4, e1), (6, e1), (15, e1)],
    [(6, e1), (16, e1)],
    [(0, e1), (11, e1), (17, e1)],
    [(0, e1), (1, e1), (3, e1), (4, e1), (7, e1), (12, e1), (13, e1), (18, e1)],
    [(0, e1), (5, e1), (9, e1), (10, e1), (19, e1)],
    [(2, e1), (4, e1), (15, e1), (20, e1)],
    [(0, e1), (7, e1), (10, e1), (21, e1)],
    [(1, e1), (2, e1), (3, e1), (8, e1), (13, e1), (14, e1), (22, e1)],
    [(5, e1), (9, e1), (11, e1), (19, e1), (23, e1)],
    [(1, e1), (3, e1), (4, e1), (12, e1), (13, e1), (17, e1), (18, e1), (24, e1)],
    [(1, e1), (3, e1), (4, e1), (8, e1), (13, e1), (15, e1), (18, e1), (22, e1), (25, e1)]])
private theorem commutator_53_left_s1 : wordMatrix [Atom.root 8 1] = atomMatrix (Atom.root 8 1) := by simp
private theorem commutator_53_left_s0 : wordMatrix [Atom.root 4 1, Atom.root 8 1] = commutator_53_target := by
  rw [wordMatrix_cons, commutator_53_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 4 1))
  decide +kernel
private theorem commutator_53_left : wordMatrix [Atom.root 4 1, Atom.root 8 1] = commutator_53_target := commutator_53_left_s0
private theorem commutator_53_right_s2 : wordMatrix [Atom.root 11 1] = atomMatrix (Atom.root 11 1) := by simp
private def commutator_53_right_m1 : Mat := Sparse.eval (![[(0, e1)],
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
private theorem commutator_53_right_s1 : wordMatrix [Atom.root 4 1, Atom.root 11 1] = commutator_53_right_m1 := by
  rw [wordMatrix_cons, commutator_53_right_s2]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 4 1))
  decide +kernel
private theorem commutator_53_right_s0 : wordMatrix [Atom.root 8 1, Atom.root 4 1, Atom.root 11 1] = commutator_53_target := by
  rw [wordMatrix_cons, commutator_53_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 8 1))
  decide +kernel
private theorem commutator_53_right : wordMatrix [Atom.root 8 1, Atom.root 4 1, Atom.root 11 1] = commutator_53_target := commutator_53_right_s0
theorem commutator_53 : wordGroup (commutator_lhs 53) = wordGroup (commutator_rhs 53) := by
  apply word_eq_of_matrix_eq
  exact commutator_53_left.trans commutator_53_right.symm

end Kourovka.Problem2153.WilsonModel.RootData.Relations
