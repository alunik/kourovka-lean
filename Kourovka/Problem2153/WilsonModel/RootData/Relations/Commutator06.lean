import Kourovka.Problem2153.WilsonModel.RootData.Relations.Metadata
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
namespace Kourovka.Problem2153.WilsonModel.RootData.Relations
open Field8 F8
private def commutator_36_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(0, e1), (2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(0, e7), (2, e1), (5, e1)],
    [(3, e1), (6, e1)],
    [(7, e1)],
    [(0, e3), (2, e6), (5, e1), (8, e1)],
    [(4, e1), (9, e1)],
    [(3, e7), (6, e1), (10, e1)],
    [(11, e1)],
    [(4, e6), (9, e1), (12, e1)],
    [(4, e6), (9, e1), (13, e1)],
    [(3, e3), (6, e6), (10, e1), (14, e1)],
    [(11, e1), (15, e1)],
    [(4, e5), (9, e1), (12, e1), (13, e1), (16, e1)],
    [(17, e1)],
    [(18, e1)],
    [(11, e7), (15, e1), (19, e1)],
    [(17, e1), (20, e1)],
    [(4, e7), (9, e4), (12, e7), (13, e7), (16, e1), (21, e1)],
    [(11, e3), (15, e6), (19, e1), (22, e1)],
    [(17, e7), (20, e1), (23, e1)],
    [(24, e1)],
    [(17, e3), (20, e6), (23, e1), (25, e1)]])
private theorem commutator_36_left_s1 : wordMatrix [Atom.root 7 6] = atomMatrix (Atom.root 7 6) := by simp
private theorem commutator_36_left_s0 : wordMatrix [Atom.root 2 1, Atom.root 7 6] = commutator_36_target := by
  rw [wordMatrix_cons, commutator_36_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 2 1))
  decide +kernel
private theorem commutator_36_left : wordMatrix [Atom.root 2 1, Atom.root 7 6] = commutator_36_target := commutator_36_left_s0
private theorem commutator_36_right_s1 : wordMatrix [Atom.root 2 1] = atomMatrix (Atom.root 2 1) := by simp
private theorem commutator_36_right_s0 : wordMatrix [Atom.root 7 6, Atom.root 2 1] = commutator_36_target := by
  rw [wordMatrix_cons, commutator_36_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 7 6))
  decide +kernel
private theorem commutator_36_right : wordMatrix [Atom.root 7 6, Atom.root 2 1] = commutator_36_target := commutator_36_right_s0
theorem commutator_36 : wordGroup (commutator_lhs 36) = wordGroup (commutator_rhs 36) := by
  apply word_eq_of_matrix_eq
  exact commutator_36_left.trans commutator_36_right.symm

private def commutator_37_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(0, e1), (2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(0, e6), (2, e1), (5, e1)],
    [(3, e1), (6, e1)],
    [(7, e1)],
    [(0, e3), (2, e7), (5, e1), (8, e1)],
    [(4, e1), (9, e1)],
    [(3, e6), (6, e1), (10, e1)],
    [(11, e1)],
    [(4, e7), (9, e1), (12, e1)],
    [(4, e7), (9, e1), (13, e1)],
    [(3, e3), (6, e7), (10, e1), (14, e1)],
    [(11, e1), (15, e1)],
    [(4, e4), (9, e1), (12, e1), (13, e1), (16, e1)],
    [(17, e1)],
    [(18, e1)],
    [(11, e6), (15, e1), (19, e1)],
    [(17, e1), (20, e1)],
    [(4, e7), (9, e5), (12, e6), (13, e6), (16, e1), (21, e1)],
    [(11, e3), (15, e7), (19, e1), (22, e1)],
    [(17, e6), (20, e1), (23, e1)],
    [(24, e1)],
    [(17, e3), (20, e7), (23, e1), (25, e1)]])
private theorem commutator_37_left_s1 : wordMatrix [Atom.root 7 7] = atomMatrix (Atom.root 7 7) := by simp
private theorem commutator_37_left_s0 : wordMatrix [Atom.root 2 1, Atom.root 7 7] = commutator_37_target := by
  rw [wordMatrix_cons, commutator_37_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 2 1))
  decide +kernel
private theorem commutator_37_left : wordMatrix [Atom.root 2 1, Atom.root 7 7] = commutator_37_target := commutator_37_left_s0
private theorem commutator_37_right_s1 : wordMatrix [Atom.root 2 1] = atomMatrix (Atom.root 2 1) := by simp
private theorem commutator_37_right_s0 : wordMatrix [Atom.root 7 7, Atom.root 2 1] = commutator_37_target := by
  rw [wordMatrix_cons, commutator_37_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 7 7))
  decide +kernel
private theorem commutator_37_right : wordMatrix [Atom.root 7 7, Atom.root 2 1] = commutator_37_target := commutator_37_right_s0
theorem commutator_37 : wordGroup (commutator_lhs 37) = wordGroup (commutator_rhs 37) := by
  apply word_eq_of_matrix_eq
  exact commutator_37_left.trans commutator_37_right.symm

private def commutator_38_target : Mat := Sparse.eval (![[(0, e1)],
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
private theorem commutator_38_left_s1 : wordMatrix [Atom.root 8 1] = atomMatrix (Atom.root 8 1) := by simp
private theorem commutator_38_left_s0 : wordMatrix [Atom.root 2 1, Atom.root 8 1] = commutator_38_target := by
  rw [wordMatrix_cons, commutator_38_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 2 1))
  decide +kernel
private theorem commutator_38_left : wordMatrix [Atom.root 2 1, Atom.root 8 1] = commutator_38_target := commutator_38_left_s0
private theorem commutator_38_right_s1 : wordMatrix [Atom.root 2 1] = atomMatrix (Atom.root 2 1) := by simp
private theorem commutator_38_right_s0 : wordMatrix [Atom.root 8 1, Atom.root 2 1] = commutator_38_target := by
  rw [wordMatrix_cons, commutator_38_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 8 1))
  decide +kernel
private theorem commutator_38_right : wordMatrix [Atom.root 8 1, Atom.root 2 1] = commutator_38_target := commutator_38_right_s0
theorem commutator_38 : wordGroup (commutator_lhs 38) = wordGroup (commutator_rhs 38) := by
  apply word_eq_of_matrix_eq
  exact commutator_38_left.trans commutator_38_right.symm

private def commutator_39_target : Mat := Sparse.eval (![[(0, e1)],
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
    [(11, e1)],
    [(0, e1), (2, e1), (9, e1), (12, e1)],
    [(0, e1), (9, e1), (13, e1)],
    [(1, e1), (3, e1), (10, e1), (14, e1)],
    [(0, e1), (11, e1), (15, e1)],
    [(0, e1), (1, e1), (2, e1), (4, e1), (9, e1), (12, e1), (13, e1), (16, e1)],
    [(4, e1), (17, e1)],
    [(6, e1), (18, e1)],
    [(0, e1), (7, e1), (11, e1), (15, e1), (19, e1)],
    [(3, e1), (4, e1), (17, e1), (20, e1)],
    [(1, e1), (2, e1), (4, e1), (8, e1), (12, e1), (13, e1), (16, e1), (21, e1)],
    [(5, e1), (7, e1), (11, e1), (19, e1), (22, e1)],
    [(2, e1), (3, e1), (4, e1), (13, e1), (17, e1), (20, e1), (23, e1)],
    [(0, e1), (9, e1), (15, e1), (24, e1)],
    [(1, e1), (2, e1), (4, e1), (10, e1), (13, e1), (16, e1), (17, e1), (23, e1), (25, e1)]])
private theorem commutator_39_left_s1 : wordMatrix [Atom.root 9 1] = atomMatrix (Atom.root 9 1) := by simp
private theorem commutator_39_left_s0 : wordMatrix [Atom.root 2 1, Atom.root 9 1] = commutator_39_target := by
  rw [wordMatrix_cons, commutator_39_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 2 1))
  decide +kernel
private theorem commutator_39_left : wordMatrix [Atom.root 2 1, Atom.root 9 1] = commutator_39_target := commutator_39_left_s0
private theorem commutator_39_right_s2 : wordMatrix [Atom.root 11 1] = atomMatrix (Atom.root 11 1) := by simp
private def commutator_39_right_m1 : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(0, e1), (2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(0, e1), (2, e1), (5, e1)],
    [(3, e1), (6, e1)],
    [(7, e1)],
    [(0, e1), (5, e1), (8, e1)],
    [(4, e1), (9, e1)],
    [(3, e1), (6, e1), (10, e1)],
    [(11, e1)],
    [(9, e1), (12, e1)],
    [(0, e1), (9, e1), (13, e1)],
    [(1, e1), (3, e1), (10, e1), (14, e1)],
    [(11, e1), (15, e1)],
    [(0, e1), (2, e1), (4, e1), (9, e1), (12, e1), (13, e1), (16, e1)],
    [(17, e1)],
    [(3, e1), (18, e1)],
    [(0, e1), (11, e1), (15, e1), (19, e1)],
    [(4, e1), (17, e1), (20, e1)],
    [(0, e1), (1, e1), (2, e1), (4, e1), (5, e1), (12, e1), (13, e1), (16, e1), (21, e1)],
    [(0, e1), (2, e1), (7, e1), (11, e1), (19, e1), (22, e1)],
    [(3, e1), (4, e1), (9, e1), (17, e1), (20, e1), (23, e1)],
    [(4, e1), (11, e1), (24, e1)],
    [(0, e1), (3, e1), (6, e1), (9, e1), (12, e1), (17, e1), (23, e1), (25, e1)]])
private theorem commutator_39_right_s1 : wordMatrix [Atom.root 2 1, Atom.root 11 1] = commutator_39_right_m1 := by
  rw [wordMatrix_cons, commutator_39_right_s2]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 2 1))
  decide +kernel
private theorem commutator_39_right_s0 : wordMatrix [Atom.root 9 1, Atom.root 2 1, Atom.root 11 1] = commutator_39_target := by
  rw [wordMatrix_cons, commutator_39_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 9 1))
  decide +kernel
private theorem commutator_39_right : wordMatrix [Atom.root 9 1, Atom.root 2 1, Atom.root 11 1] = commutator_39_target := commutator_39_right_s0
theorem commutator_39 : wordGroup (commutator_lhs 39) = wordGroup (commutator_rhs 39) := by
  apply word_eq_of_matrix_eq
  exact commutator_39_left.trans commutator_39_right.symm

private def commutator_40_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(0, e1), (2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(0, e1), (2, e1), (5, e1)],
    [(3, e1), (6, e1)],
    [(7, e1)],
    [(0, e1), (5, e1), (8, e1)],
    [(4, e1), (9, e1)],
    [(3, e1), (6, e1), (10, e1)],
    [(0, e1), (11, e1)],
    [(1, e1), (9, e1), (12, e1)],
    [(1, e1), (9, e1), (13, e1)],
    [(3, e1), (10, e1), (14, e1)],
    [(0, e1), (2, e1), (11, e1), (15, e1)],
    [(4, e1), (9, e1), (12, e1), (13, e1), (16, e1)],
    [(0, e1), (3, e1), (17, e1)],
    [(1, e1), (18, e1)],
    [(0, e1), (2, e1), (5, e1), (11, e1), (15, e1), (19, e1)],
    [(0, e1), (2, e1), (3, e1), (6, e1), (17, e1), (20, e1)],
    [(4, e1), (12, e1), (13, e1), (16, e1), (21, e1)],
    [(0, e1), (5, e1), (8, e1), (11, e1), (19, e1), (22, e1)],
    [(0, e1), (2, e1), (3, e1), (5, e1), (6, e1), (10, e1), (17, e1), (20, e1), (23, e1)],
    [(1, e1), (7, e1), (12, e1), (13, e1), (24, e1)],
    [(0, e1), (3, e1), (5, e1), (8, e1), (10, e1), (14, e1), (17, e1), (23, e1), (25, e1)]])
private theorem commutator_40_left_s1 : wordMatrix [Atom.root 10 1] = atomMatrix (Atom.root 10 1) := by simp
private theorem commutator_40_left_s0 : wordMatrix [Atom.root 2 1, Atom.root 10 1] = commutator_40_target := by
  rw [wordMatrix_cons, commutator_40_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 2 1))
  decide +kernel
private theorem commutator_40_left : wordMatrix [Atom.root 2 1, Atom.root 10 1] = commutator_40_target := commutator_40_left_s0
private theorem commutator_40_right_s1 : wordMatrix [Atom.root 2 1] = atomMatrix (Atom.root 2 1) := by simp
private theorem commutator_40_right_s0 : wordMatrix [Atom.root 10 1, Atom.root 2 1] = commutator_40_target := by
  rw [wordMatrix_cons, commutator_40_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 10 1))
  decide +kernel
private theorem commutator_40_right : wordMatrix [Atom.root 10 1, Atom.root 2 1] = commutator_40_target := commutator_40_right_s0
theorem commutator_40 : wordGroup (commutator_lhs 40) = wordGroup (commutator_rhs 40) := by
  apply word_eq_of_matrix_eq
  exact commutator_40_left.trans commutator_40_right.symm

private def commutator_41_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(0, e1), (2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(0, e1), (2, e1), (5, e1)],
    [(3, e1), (6, e1)],
    [(7, e1)],
    [(0, e1), (5, e1), (8, e1)],
    [(4, e1), (9, e1)],
    [(3, e1), (6, e1), (10, e1)],
    [(11, e1)],
    [(9, e1), (12, e1)],
    [(0, e1), (9, e1), (13, e1)],
    [(1, e1), (3, e1), (10, e1), (14, e1)],
    [(11, e1), (15, e1)],
    [(0, e1), (2, e1), (4, e1), (9, e1), (12, e1), (13, e1), (16, e1)],
    [(17, e1)],
    [(3, e1), (18, e1)],
    [(0, e1), (11, e1), (15, e1), (19, e1)],
    [(4, e1), (17, e1), (20, e1)],
    [(0, e1), (1, e1), (2, e1), (4, e1), (5, e1), (12, e1), (13, e1), (16, e1), (21, e1)],
    [(0, e1), (2, e1), (7, e1), (11, e1), (19, e1), (22, e1)],
    [(3, e1), (4, e1), (9, e1), (17, e1), (20, e1), (23, e1)],
    [(4, e1), (11, e1), (24, e1)],
    [(0, e1), (3, e1), (6, e1), (9, e1), (12, e1), (17, e1), (23, e1), (25, e1)]])
private theorem commutator_41_left_s1 : wordMatrix [Atom.root 11 1] = atomMatrix (Atom.root 11 1) := by simp
private theorem commutator_41_left_s0 : wordMatrix [Atom.root 2 1, Atom.root 11 1] = commutator_41_target := by
  rw [wordMatrix_cons, commutator_41_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 2 1))
  decide +kernel
private theorem commutator_41_left : wordMatrix [Atom.root 2 1, Atom.root 11 1] = commutator_41_target := commutator_41_left_s0
private theorem commutator_41_right_s1 : wordMatrix [Atom.root 2 1] = atomMatrix (Atom.root 2 1) := by simp
private theorem commutator_41_right_s0 : wordMatrix [Atom.root 11 1, Atom.root 2 1] = commutator_41_target := by
  rw [wordMatrix_cons, commutator_41_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 11 1))
  decide +kernel
private theorem commutator_41_right : wordMatrix [Atom.root 11 1, Atom.root 2 1] = commutator_41_target := commutator_41_right_s0
theorem commutator_41 : wordGroup (commutator_lhs 41) = wordGroup (commutator_rhs 41) := by
  apply word_eq_of_matrix_eq
  exact commutator_41_left.trans commutator_41_right.symm

end Kourovka.Problem2153.WilsonModel.RootData.Relations
