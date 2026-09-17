import Kourovka.Problem2153.WilsonModel.RootData.Relations.Metadata
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
namespace Kourovka.Problem2153.WilsonModel.RootData.Relations
open Field8 F8
private def commutator_84_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(5, e1)],
    [(6, e1)],
    [(0, e1), (7, e1)],
    [(1, e1), (8, e1)],
    [(0, e1), (9, e1)],
    [(0, e1), (1, e1), (10, e1)],
    [(11, e1)],
    [(2, e1), (3, e1), (12, e1)],
    [(13, e1)],
    [(2, e1), (14, e1)],
    [(0, e1), (4, e1), (15, e1)],
    [(1, e1), (6, e1), (16, e1)],
    [(4, e1), (17, e1)],
    [(4, e1), (6, e1), (18, e1)],
    [(0, e1), (7, e1), (9, e1), (19, e1)],
    [(3, e1), (20, e1)],
    [(0, e1), (1, e1), (7, e1), (8, e1), (10, e1), (21, e1)],
    [(3, e1), (5, e1), (13, e1), (22, e1)],
    [(2, e1), (11, e1), (13, e1), (23, e1)],
    [(0, e1), (4, e1), (9, e1), (15, e1), (17, e1), (24, e1)],
    [(0, e1), (1, e1), (4, e1), (6, e1), (10, e1), (15, e1), (16, e1), (18, e1), (25, e1)]])
private theorem commutator_84_left_s1 : wordMatrix [Atom.root 9 1] = atomMatrix (Atom.root 9 1) := by simp
private theorem commutator_84_left_s0 : wordMatrix [Atom.root 8 1, Atom.root 9 1] = commutator_84_target := by
  rw [wordMatrix_cons, commutator_84_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 8 1))
  decide +kernel
private theorem commutator_84_left : wordMatrix [Atom.root 8 1, Atom.root 9 1] = commutator_84_target := commutator_84_left_s0
private theorem commutator_84_right_s1 : wordMatrix [Atom.root 8 1] = atomMatrix (Atom.root 8 1) := by simp
private theorem commutator_84_right_s0 : wordMatrix [Atom.root 9 1, Atom.root 8 1] = commutator_84_target := by
  rw [wordMatrix_cons, commutator_84_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 9 1))
  decide +kernel
private theorem commutator_84_right : wordMatrix [Atom.root 9 1, Atom.root 8 1] = commutator_84_target := commutator_84_right_s0
theorem commutator_84 : wordGroup (commutator_lhs 84) = wordGroup (commutator_rhs 84) := by
  apply word_eq_of_matrix_eq
  exact commutator_84_left.trans commutator_84_right.symm

private def commutator_85_target : Mat := Sparse.eval (![[(0, e1)],
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
    [(1, e1), (13, e1)],
    [(2, e1), (14, e1)],
    [(2, e1), (4, e1), (15, e1)],
    [(6, e1), (16, e1)],
    [(0, e1), (3, e1), (17, e1)],
    [(1, e1), (4, e1), (18, e1)],
    [(5, e1), (9, e1), (19, e1)],
    [(2, e1), (6, e1), (20, e1)],
    [(0, e1), (7, e1), (10, e1), (21, e1)],
    [(1, e1), (3, e1), (8, e1), (13, e1), (22, e1)],
    [(0, e1), (5, e1), (10, e1), (11, e1), (23, e1)],
    [(0, e1), (1, e1), (3, e1), (7, e1), (12, e1), (13, e1), (17, e1), (24, e1)],
    [(1, e1), (2, e1), (4, e1), (8, e1), (14, e1), (15, e1), (18, e1), (25, e1)]])
private theorem commutator_85_left_s1 : wordMatrix [Atom.root 10 1] = atomMatrix (Atom.root 10 1) := by simp
private theorem commutator_85_left_s0 : wordMatrix [Atom.root 8 1, Atom.root 10 1] = commutator_85_target := by
  rw [wordMatrix_cons, commutator_85_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 8 1))
  decide +kernel
private theorem commutator_85_left : wordMatrix [Atom.root 8 1, Atom.root 10 1] = commutator_85_target := commutator_85_left_s0
private theorem commutator_85_right_s1 : wordMatrix [Atom.root 8 1] = atomMatrix (Atom.root 8 1) := by simp
private theorem commutator_85_right_s0 : wordMatrix [Atom.root 10 1, Atom.root 8 1] = commutator_85_target := by
  rw [wordMatrix_cons, commutator_85_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 10 1))
  decide +kernel
private theorem commutator_85_right : wordMatrix [Atom.root 10 1, Atom.root 8 1] = commutator_85_target := commutator_85_right_s0
theorem commutator_85 : wordGroup (commutator_lhs 85) = wordGroup (commutator_rhs 85) := by
  apply word_eq_of_matrix_eq
  exact commutator_85_left.trans commutator_85_right.symm

private def commutator_86_target : Mat := Sparse.eval (![[(0, e1)],
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
    [(11, e1)],
    [(3, e1), (12, e1)],
    [(0, e1), (13, e1)],
    [(1, e1), (2, e1), (14, e1)],
    [(4, e1), (15, e1)],
    [(2, e1), (6, e1), (16, e1)],
    [(17, e1)],
    [(3, e1), (4, e1), (18, e1)],
    [(0, e1), (9, e1), (19, e1)],
    [(4, e1), (20, e1)],
    [(0, e1), (1, e1), (5, e1), (7, e1), (10, e1), (21, e1)],
    [(0, e1), (2, e1), (3, e1), (7, e1), (13, e1), (22, e1)],
    [(3, e1), (9, e1), (11, e1), (23, e1)],
    [(4, e1), (11, e1), (17, e1), (24, e1)],
    [(0, e1), (3, e1), (4, e1), (6, e1), (12, e1), (15, e1), (18, e1), (25, e1)]])
private theorem commutator_86_left_s1 : wordMatrix [Atom.root 11 1] = atomMatrix (Atom.root 11 1) := by simp
private theorem commutator_86_left_s0 : wordMatrix [Atom.root 8 1, Atom.root 11 1] = commutator_86_target := by
  rw [wordMatrix_cons, commutator_86_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 8 1))
  decide +kernel
private theorem commutator_86_left : wordMatrix [Atom.root 8 1, Atom.root 11 1] = commutator_86_target := commutator_86_left_s0
private theorem commutator_86_right_s1 : wordMatrix [Atom.root 8 1] = atomMatrix (Atom.root 8 1) := by simp
private theorem commutator_86_right_s0 : wordMatrix [Atom.root 11 1, Atom.root 8 1] = commutator_86_target := by
  rw [wordMatrix_cons, commutator_86_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 11 1))
  decide +kernel
private theorem commutator_86_right : wordMatrix [Atom.root 11 1, Atom.root 8 1] = commutator_86_target := commutator_86_right_s0
theorem commutator_86 : wordGroup (commutator_lhs 86) = wordGroup (commutator_rhs 86) := by
  apply word_eq_of_matrix_eq
  exact commutator_86_left.trans commutator_86_right.symm

private def commutator_87_target : Mat := Sparse.eval (![[(0, e1)],
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
    [(1, e1), (13, e1)],
    [(14, e1)],
    [(0, e1), (2, e1), (15, e1)],
    [(1, e1), (16, e1)],
    [(0, e1), (3, e1), (4, e1), (17, e1)],
    [(1, e1), (6, e1), (18, e1)],
    [(5, e1), (7, e1), (19, e1)],
    [(2, e1), (3, e1), (6, e1), (20, e1)],
    [(8, e1), (21, e1)],
    [(5, e1), (8, e1), (22, e1)],
    [(1, e1), (2, e1), (5, e1), (10, e1), (13, e1), (23, e1)],
    [(0, e1), (1, e1), (2, e1), (7, e1), (9, e1), (12, e1), (13, e1), (15, e1), (24, e1)],
    [(1, e1), (8, e1), (10, e1), (14, e1), (16, e1), (25, e1)]])
private theorem commutator_87_left_s1 : wordMatrix [Atom.root 10 1] = atomMatrix (Atom.root 10 1) := by simp
private theorem commutator_87_left_s0 : wordMatrix [Atom.root 9 1, Atom.root 10 1] = commutator_87_target := by
  rw [wordMatrix_cons, commutator_87_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 9 1))
  decide +kernel
private theorem commutator_87_left : wordMatrix [Atom.root 9 1, Atom.root 10 1] = commutator_87_target := commutator_87_left_s0
private theorem commutator_87_right_s1 : wordMatrix [Atom.root 9 1] = atomMatrix (Atom.root 9 1) := by simp
private theorem commutator_87_right_s0 : wordMatrix [Atom.root 10 1, Atom.root 9 1] = commutator_87_target := by
  rw [wordMatrix_cons, commutator_87_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 10 1))
  decide +kernel
private theorem commutator_87_right : wordMatrix [Atom.root 10 1, Atom.root 9 1] = commutator_87_target := commutator_87_right_s0
theorem commutator_87 : wordGroup (commutator_lhs 87) = wordGroup (commutator_rhs 87) := by
  apply word_eq_of_matrix_eq
  exact commutator_87_left.trans commutator_87_right.symm

private def commutator_88_target : Mat := Sparse.eval (![[(0, e1)],
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
    [(11, e1)],
    [(2, e1), (12, e1)],
    [(0, e1), (13, e1)],
    [(1, e1), (14, e1)],
    [(0, e1), (15, e1)],
    [(1, e1), (2, e1), (16, e1)],
    [(4, e1), (17, e1)],
    [(3, e1), (6, e1), (18, e1)],
    [(0, e1), (7, e1), (19, e1)],
    [(3, e1), (4, e1), (20, e1)],
    [(1, e1), (5, e1), (8, e1), (21, e1)],
    [(2, e1), (5, e1), (7, e1), (22, e1)],
    [(0, e1), (2, e1), (3, e1), (9, e1), (13, e1), (23, e1)],
    [(0, e1), (4, e1), (9, e1), (11, e1), (15, e1), (24, e1)],
    [(0, e1), (1, e1), (2, e1), (6, e1), (10, e1), (12, e1), (16, e1), (25, e1)]])
private theorem commutator_88_left_s1 : wordMatrix [Atom.root 11 1] = atomMatrix (Atom.root 11 1) := by simp
private theorem commutator_88_left_s0 : wordMatrix [Atom.root 9 1, Atom.root 11 1] = commutator_88_target := by
  rw [wordMatrix_cons, commutator_88_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 9 1))
  decide +kernel
private theorem commutator_88_left : wordMatrix [Atom.root 9 1, Atom.root 11 1] = commutator_88_target := commutator_88_left_s0
private theorem commutator_88_right_s1 : wordMatrix [Atom.root 9 1] = atomMatrix (Atom.root 9 1) := by simp
private theorem commutator_88_right_s0 : wordMatrix [Atom.root 11 1, Atom.root 9 1] = commutator_88_target := by
  rw [wordMatrix_cons, commutator_88_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 11 1))
  decide +kernel
private theorem commutator_88_right : wordMatrix [Atom.root 11 1, Atom.root 9 1] = commutator_88_target := commutator_88_right_s0
theorem commutator_88 : wordGroup (commutator_lhs 88) = wordGroup (commutator_rhs 88) := by
  apply word_eq_of_matrix_eq
  exact commutator_88_left.trans commutator_88_right.symm

private def commutator_89_target : Mat := Sparse.eval (![[(0, e1)],
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
private theorem commutator_89_left_s1 : wordMatrix [Atom.root 11 1] = atomMatrix (Atom.root 11 1) := by simp
private theorem commutator_89_left_s0 : wordMatrix [Atom.root 10 1, Atom.root 11 1] = commutator_89_target := by
  rw [wordMatrix_cons, commutator_89_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 10 1))
  decide +kernel
private theorem commutator_89_left : wordMatrix [Atom.root 10 1, Atom.root 11 1] = commutator_89_target := commutator_89_left_s0
private theorem commutator_89_right_s1 : wordMatrix [Atom.root 10 1] = atomMatrix (Atom.root 10 1) := by simp
private theorem commutator_89_right_s0 : wordMatrix [Atom.root 11 1, Atom.root 10 1] = commutator_89_target := by
  rw [wordMatrix_cons, commutator_89_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 11 1))
  decide +kernel
private theorem commutator_89_right : wordMatrix [Atom.root 11 1, Atom.root 10 1] = commutator_89_target := commutator_89_right_s0
theorem commutator_89 : wordGroup (commutator_lhs 89) = wordGroup (commutator_rhs 89) := by
  apply word_eq_of_matrix_eq
  exact commutator_89_left.trans commutator_89_right.symm

end Kourovka.Problem2153.WilsonModel.RootData.Relations
