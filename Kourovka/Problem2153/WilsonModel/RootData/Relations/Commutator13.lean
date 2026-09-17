import Kourovka.Problem2153.WilsonModel.RootData.Relations.Metadata
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
namespace Kourovka.Problem2153.WilsonModel.RootData.Relations
open Field8 F8
private def commutator_78_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(1, e1), (5, e1)],
    [(0, e1), (6, e1)],
    [(2, e1), (7, e1)],
    [(8, e1)],
    [(3, e1), (9, e1)],
    [(10, e1)],
    [(4, e1), (11, e1)],
    [(12, e1)],
    [(0, e6), (6, e1), (13, e1)],
    [(1, e7), (5, e1), (14, e1)],
    [(15, e1)],
    [(2, e7), (7, e1), (16, e1)],
    [(17, e1)],
    [(3, e7), (9, e1), (18, e1)],
    [(0, e5), (6, e1), (12, e1), (19, e1)],
    [(4, e7), (11, e1), (20, e1)],
    [(1, e3), (5, e6), (14, e1), (21, e1)],
    [(2, e3), (7, e6), (16, e1), (22, e1)],
    [(3, e3), (9, e6), (18, e1), (23, e1)],
    [(4, e3), (11, e6), (20, e1), (24, e1)],
    [(0, e7), (6, e4), (12, e7), (19, e1), (25, e1)]])
private theorem commutator_78_left_s1 : wordMatrix [Atom.root 11 6] = atomMatrix (Atom.root 11 6) := by simp
private theorem commutator_78_left_s0 : wordMatrix [Atom.root 6 1, Atom.root 11 6] = commutator_78_target := by
  rw [wordMatrix_cons, commutator_78_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 6 1))
  decide +kernel
private theorem commutator_78_left : wordMatrix [Atom.root 6 1, Atom.root 11 6] = commutator_78_target := commutator_78_left_s0
private theorem commutator_78_right_s1 : wordMatrix [Atom.root 6 1] = atomMatrix (Atom.root 6 1) := by simp
private theorem commutator_78_right_s0 : wordMatrix [Atom.root 11 6, Atom.root 6 1] = commutator_78_target := by
  rw [wordMatrix_cons, commutator_78_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 11 6))
  decide +kernel
private theorem commutator_78_right : wordMatrix [Atom.root 11 6, Atom.root 6 1] = commutator_78_target := commutator_78_right_s0
theorem commutator_78 : wordGroup (commutator_lhs 78) = wordGroup (commutator_rhs 78) := by
  apply word_eq_of_matrix_eq
  exact commutator_78_left.trans commutator_78_right.symm

private def commutator_79_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(1, e1), (5, e1)],
    [(0, e1), (6, e1)],
    [(2, e1), (7, e1)],
    [(8, e1)],
    [(3, e1), (9, e1)],
    [(10, e1)],
    [(4, e1), (11, e1)],
    [(12, e1)],
    [(0, e7), (6, e1), (13, e1)],
    [(1, e6), (5, e1), (14, e1)],
    [(15, e1)],
    [(2, e6), (7, e1), (16, e1)],
    [(17, e1)],
    [(3, e6), (9, e1), (18, e1)],
    [(0, e4), (6, e1), (12, e1), (19, e1)],
    [(4, e6), (11, e1), (20, e1)],
    [(1, e3), (5, e7), (14, e1), (21, e1)],
    [(2, e3), (7, e7), (16, e1), (22, e1)],
    [(3, e3), (9, e7), (18, e1), (23, e1)],
    [(4, e3), (11, e7), (20, e1), (24, e1)],
    [(0, e7), (6, e5), (12, e6), (19, e1), (25, e1)]])
private theorem commutator_79_left_s1 : wordMatrix [Atom.root 11 7] = atomMatrix (Atom.root 11 7) := by simp
private theorem commutator_79_left_s0 : wordMatrix [Atom.root 6 1, Atom.root 11 7] = commutator_79_target := by
  rw [wordMatrix_cons, commutator_79_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 6 1))
  decide +kernel
private theorem commutator_79_left : wordMatrix [Atom.root 6 1, Atom.root 11 7] = commutator_79_target := commutator_79_left_s0
private theorem commutator_79_right_s1 : wordMatrix [Atom.root 6 1] = atomMatrix (Atom.root 6 1) := by simp
private theorem commutator_79_right_s0 : wordMatrix [Atom.root 11 7, Atom.root 6 1] = commutator_79_target := by
  rw [wordMatrix_cons, commutator_79_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 11 7))
  decide +kernel
private theorem commutator_79_right : wordMatrix [Atom.root 11 7, Atom.root 6 1] = commutator_79_target := commutator_79_right_s0
theorem commutator_79 : wordGroup (commutator_lhs 79) = wordGroup (commutator_rhs 79) := by
  apply word_eq_of_matrix_eq
  exact commutator_79_left.trans commutator_79_right.symm

private def commutator_80_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(0, e1), (5, e1)],
    [(6, e1)],
    [(0, e1), (7, e1)],
    [(0, e1), (1, e1), (2, e1), (8, e1)],
    [(9, e1)],
    [(0, e1), (3, e1), (10, e1)],
    [(11, e1)],
    [(3, e1), (4, e1), (12, e1)],
    [(4, e1), (13, e1)],
    [(2, e1), (3, e1), (6, e1), (14, e1)],
    [(4, e1), (15, e1)],
    [(4, e1), (6, e1), (16, e1)],
    [(17, e1)],
    [(4, e1), (18, e1)],
    [(9, e1), (11, e1), (19, e1)],
    [(20, e1)],
    [(0, e1), (3, e1), (4, e1), (7, e1), (9, e1), (10, e1), (12, e1), (13, e1), (21, e1)],
    [(3, e1), (4, e1), (11, e1), (13, e1), (15, e1), (22, e1)],
    [(11, e1), (17, e1), (23, e1)],
    [(17, e1), (24, e1)],
    [(4, e1), (15, e1), (17, e1), (18, e1), (20, e1), (25, e1)]])
private theorem commutator_80_left_s1 : wordMatrix [Atom.root 8 1] = atomMatrix (Atom.root 8 1) := by simp
private theorem commutator_80_left_s0 : wordMatrix [Atom.root 7 1, Atom.root 8 1] = commutator_80_target := by
  rw [wordMatrix_cons, commutator_80_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 7 1))
  decide +kernel
private theorem commutator_80_left : wordMatrix [Atom.root 7 1, Atom.root 8 1] = commutator_80_target := commutator_80_left_s0
private theorem commutator_80_right_s1 : wordMatrix [Atom.root 7 1] = atomMatrix (Atom.root 7 1) := by simp
private theorem commutator_80_right_s0 : wordMatrix [Atom.root 8 1, Atom.root 7 1] = commutator_80_target := by
  rw [wordMatrix_cons, commutator_80_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 8 1))
  decide +kernel
private theorem commutator_80_right : wordMatrix [Atom.root 8 1, Atom.root 7 1] = commutator_80_target := commutator_80_right_s0
theorem commutator_80 : wordGroup (commutator_lhs 80) = wordGroup (commutator_rhs 80) := by
  apply word_eq_of_matrix_eq
  exact commutator_80_left.trans commutator_80_right.symm

private def commutator_81_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(0, e1), (5, e1)],
    [(6, e1)],
    [(7, e1)],
    [(0, e1), (2, e1), (8, e1)],
    [(0, e1), (9, e1)],
    [(1, e1), (3, e1), (10, e1)],
    [(11, e1)],
    [(2, e1), (4, e1), (12, e1)],
    [(4, e1), (13, e1)],
    [(3, e1), (6, e1), (14, e1)],
    [(0, e1), (15, e1)],
    [(1, e1), (4, e1), (16, e1)],
    [(4, e1), (17, e1)],
    [(6, e1), (18, e1)],
    [(7, e1), (11, e1), (19, e1)],
    [(3, e1), (20, e1)],
    [(0, e1), (2, e1), (4, e1), (8, e1), (9, e1), (12, e1), (13, e1), (21, e1)],
    [(0, e1), (5, e1), (11, e1), (15, e1), (22, e1)],
    [(2, e1), (4, e1), (13, e1), (17, e1), (23, e1)],
    [(0, e1), (9, e1), (15, e1), (24, e1)],
    [(1, e1), (3, e1), (4, e1), (10, e1), (16, e1), (17, e1), (20, e1), (25, e1)]])
private theorem commutator_81_left_s1 : wordMatrix [Atom.root 9 1] = atomMatrix (Atom.root 9 1) := by simp
private theorem commutator_81_left_s0 : wordMatrix [Atom.root 7 1, Atom.root 9 1] = commutator_81_target := by
  rw [wordMatrix_cons, commutator_81_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 7 1))
  decide +kernel
private theorem commutator_81_left : wordMatrix [Atom.root 7 1, Atom.root 9 1] = commutator_81_target := commutator_81_left_s0
private theorem commutator_81_right_s1 : wordMatrix [Atom.root 7 1] = atomMatrix (Atom.root 7 1) := by simp
private theorem commutator_81_right_s0 : wordMatrix [Atom.root 9 1, Atom.root 7 1] = commutator_81_target := by
  rw [wordMatrix_cons, commutator_81_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 9 1))
  decide +kernel
private theorem commutator_81_right : wordMatrix [Atom.root 9 1, Atom.root 7 1] = commutator_81_target := commutator_81_right_s0
theorem commutator_81 : wordGroup (commutator_lhs 81) = wordGroup (commutator_rhs 81) := by
  apply word_eq_of_matrix_eq
  exact commutator_81_left.trans commutator_81_right.symm

private def commutator_82_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(0, e1), (5, e1)],
    [(6, e1)],
    [(7, e1)],
    [(0, e1), (2, e1), (8, e1)],
    [(9, e1)],
    [(3, e1), (10, e1)],
    [(0, e1), (11, e1)],
    [(1, e1), (4, e1), (12, e1)],
    [(1, e1), (4, e1), (13, e1)],
    [(3, e1), (6, e1), (14, e1)],
    [(2, e1), (15, e1)],
    [(4, e1), (16, e1)],
    [(0, e1), (3, e1), (17, e1)],
    [(1, e1), (18, e1)],
    [(0, e1), (5, e1), (11, e1), (19, e1)],
    [(2, e1), (6, e1), (20, e1)],
    [(4, e1), (9, e1), (12, e1), (13, e1), (21, e1)],
    [(0, e1), (2, e1), (8, e1), (11, e1), (15, e1), (22, e1)],
    [(0, e1), (3, e1), (5, e1), (10, e1), (17, e1), (23, e1)],
    [(1, e1), (7, e1), (12, e1), (13, e1), (24, e1)],
    [(0, e1), (2, e1), (3, e1), (6, e1), (8, e1), (14, e1), (17, e1), (20, e1), (25, e1)]])
private theorem commutator_82_left_s1 : wordMatrix [Atom.root 10 1] = atomMatrix (Atom.root 10 1) := by simp
private theorem commutator_82_left_s0 : wordMatrix [Atom.root 7 1, Atom.root 10 1] = commutator_82_target := by
  rw [wordMatrix_cons, commutator_82_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 7 1))
  decide +kernel
private theorem commutator_82_left : wordMatrix [Atom.root 7 1, Atom.root 10 1] = commutator_82_target := commutator_82_left_s0
private theorem commutator_82_right_s1 : wordMatrix [Atom.root 7 1] = atomMatrix (Atom.root 7 1) := by simp
private theorem commutator_82_right_s0 : wordMatrix [Atom.root 10 1, Atom.root 7 1] = commutator_82_target := by
  rw [wordMatrix_cons, commutator_82_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 10 1))
  decide +kernel
private theorem commutator_82_right : wordMatrix [Atom.root 10 1, Atom.root 7 1] = commutator_82_target := commutator_82_right_s0
theorem commutator_82 : wordGroup (commutator_lhs 82) = wordGroup (commutator_rhs 82) := by
  apply word_eq_of_matrix_eq
  exact commutator_82_left.trans commutator_82_right.symm

private def commutator_83_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(0, e1), (5, e1)],
    [(6, e1)],
    [(7, e1)],
    [(0, e1), (2, e1), (8, e1)],
    [(9, e1)],
    [(3, e1), (10, e1)],
    [(11, e1)],
    [(4, e1), (12, e1)],
    [(0, e1), (4, e1), (13, e1)],
    [(1, e1), (3, e1), (6, e1), (14, e1)],
    [(15, e1)],
    [(2, e1), (4, e1), (16, e1)],
    [(17, e1)],
    [(3, e1), (18, e1)],
    [(0, e1), (11, e1), (19, e1)],
    [(4, e1), (20, e1)],
    [(0, e1), (1, e1), (4, e1), (5, e1), (9, e1), (12, e1), (13, e1), (21, e1)],
    [(2, e1), (7, e1), (11, e1), (15, e1), (22, e1)],
    [(3, e1), (9, e1), (17, e1), (23, e1)],
    [(4, e1), (11, e1), (24, e1)],
    [(0, e1), (4, e1), (6, e1), (12, e1), (17, e1), (20, e1), (25, e1)]])
private theorem commutator_83_left_s1 : wordMatrix [Atom.root 11 1] = atomMatrix (Atom.root 11 1) := by simp
private theorem commutator_83_left_s0 : wordMatrix [Atom.root 7 1, Atom.root 11 1] = commutator_83_target := by
  rw [wordMatrix_cons, commutator_83_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 7 1))
  decide +kernel
private theorem commutator_83_left : wordMatrix [Atom.root 7 1, Atom.root 11 1] = commutator_83_target := commutator_83_left_s0
private theorem commutator_83_right_s1 : wordMatrix [Atom.root 7 1] = atomMatrix (Atom.root 7 1) := by simp
private theorem commutator_83_right_s0 : wordMatrix [Atom.root 11 1, Atom.root 7 1] = commutator_83_target := by
  rw [wordMatrix_cons, commutator_83_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 11 1))
  decide +kernel
private theorem commutator_83_right : wordMatrix [Atom.root 11 1, Atom.root 7 1] = commutator_83_target := commutator_83_right_s0
theorem commutator_83 : wordGroup (commutator_lhs 83) = wordGroup (commutator_rhs 83) := by
  apply word_eq_of_matrix_eq
  exact commutator_83_left.trans commutator_83_right.symm

end Kourovka.Problem2153.WilsonModel.RootData.Relations
