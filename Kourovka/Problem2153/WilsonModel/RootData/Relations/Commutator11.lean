import Kourovka.Problem2153.WilsonModel.RootData.Relations.Metadata
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
namespace Kourovka.Problem2153.WilsonModel.RootData.Relations
open Field8 F8
private def commutator_66_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(0, e1), (4, e1)],
    [(5, e1)],
    [(1, e1), (6, e1)],
    [(7, e1)],
    [(8, e1)],
    [(0, e1), (1, e1), (9, e1)],
    [(1, e1), (10, e1)],
    [(2, e1), (11, e1)],
    [(2, e1), (5, e1), (12, e1)],
    [(13, e1)],
    [(14, e1)],
    [(0, e1), (7, e1), (15, e1)],
    [(1, e1), (8, e1), (16, e1)],
    [(0, e1), (1, e1), (4, e1), (6, e1), (9, e1), (17, e1)],
    [(1, e1), (6, e1), (10, e1), (18, e1)],
    [(7, e1), (8, e1), (19, e1)],
    [(3, e1), (5, e1), (13, e1), (20, e1)],
    [(8, e1), (21, e1)],
    [(5, e1), (22, e1)],
    [(2, e1), (13, e1), (14, e1), (23, e1)],
    [(0, e1), (1, e1), (7, e1), (8, e1), (9, e1), (15, e1), (16, e1), (19, e1), (24, e1)],
    [(1, e1), (8, e1), (10, e1), (16, e1), (21, e1), (25, e1)]])
private theorem commutator_66_left_s1 : wordMatrix [Atom.root 9 1] = atomMatrix (Atom.root 9 1) := by simp
private theorem commutator_66_left_s0 : wordMatrix [Atom.root 5 1, Atom.root 9 1] = commutator_66_target := by
  rw [wordMatrix_cons, commutator_66_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 5 1))
  decide +kernel
private theorem commutator_66_left : wordMatrix [Atom.root 5 1, Atom.root 9 1] = commutator_66_target := commutator_66_left_s0
private theorem commutator_66_right_s1 : wordMatrix [Atom.root 5 1] = atomMatrix (Atom.root 5 1) := by simp
private theorem commutator_66_right_s0 : wordMatrix [Atom.root 9 1, Atom.root 5 1] = commutator_66_target := by
  rw [wordMatrix_cons, commutator_66_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 9 1))
  decide +kernel
private theorem commutator_66_right : wordMatrix [Atom.root 9 1, Atom.root 5 1] = commutator_66_target := commutator_66_right_s0
theorem commutator_66 : wordGroup (commutator_lhs 66) = wordGroup (commutator_rhs 66) := by
  apply word_eq_of_matrix_eq
  exact commutator_66_left.trans commutator_66_right.symm

private def commutator_67_target : Mat := Sparse.eval (![[(0, e1)],
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
private theorem commutator_67_left_s1 : wordMatrix [Atom.root 10 1] = atomMatrix (Atom.root 10 1) := by simp
private theorem commutator_67_left_s0 : wordMatrix [Atom.root 5 1, Atom.root 10 1] = commutator_67_target := by
  rw [wordMatrix_cons, commutator_67_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 5 1))
  decide +kernel
private theorem commutator_67_left : wordMatrix [Atom.root 5 1, Atom.root 10 1] = commutator_67_target := commutator_67_left_s0
private theorem commutator_67_right_s1 : wordMatrix [Atom.root 5 1] = atomMatrix (Atom.root 5 1) := by simp
private theorem commutator_67_right_s0 : wordMatrix [Atom.root 10 1, Atom.root 5 1] = commutator_67_target := by
  rw [wordMatrix_cons, commutator_67_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 10 1))
  decide +kernel
private theorem commutator_67_right : wordMatrix [Atom.root 10 1, Atom.root 5 1] = commutator_67_target := commutator_67_right_s0
theorem commutator_67 : wordGroup (commutator_lhs 67) = wordGroup (commutator_rhs 67) := by
  apply word_eq_of_matrix_eq
  exact commutator_67_left.trans commutator_67_right.symm

private def commutator_68_target : Mat := Sparse.eval (![[(0, e1)],
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
private theorem commutator_68_left_s1 : wordMatrix [Atom.root 11 1] = atomMatrix (Atom.root 11 1) := by simp
private theorem commutator_68_left_s0 : wordMatrix [Atom.root 5 1, Atom.root 11 1] = commutator_68_target := by
  rw [wordMatrix_cons, commutator_68_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 5 1))
  decide +kernel
private theorem commutator_68_left : wordMatrix [Atom.root 5 1, Atom.root 11 1] = commutator_68_target := commutator_68_left_s0
private theorem commutator_68_right_s1 : wordMatrix [Atom.root 5 1] = atomMatrix (Atom.root 5 1) := by simp
private theorem commutator_68_right_s0 : wordMatrix [Atom.root 11 1, Atom.root 5 1] = commutator_68_target := by
  rw [wordMatrix_cons, commutator_68_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 11 1))
  decide +kernel
private theorem commutator_68_right : wordMatrix [Atom.root 11 1, Atom.root 5 1] = commutator_68_target := commutator_68_right_s0
theorem commutator_68 : wordGroup (commutator_lhs 68) = wordGroup (commutator_rhs 68) := by
  apply word_eq_of_matrix_eq
  exact commutator_68_left.trans commutator_68_right.symm

private def commutator_69_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(0, e1), (1, e1), (5, e1)],
    [(0, e1), (6, e1)],
    [(2, e1), (7, e1)],
    [(0, e1), (2, e1), (8, e1)],
    [(3, e1), (9, e1)],
    [(3, e1), (10, e1)],
    [(4, e1), (11, e1)],
    [(4, e1), (12, e1)],
    [(4, e1), (6, e1), (13, e1)],
    [(0, e1), (1, e1), (3, e1), (5, e1), (6, e1), (14, e1)],
    [(15, e1)],
    [(2, e1), (4, e1), (7, e1), (16, e1)],
    [(17, e1)],
    [(3, e1), (9, e1), (18, e1)],
    [(0, e1), (4, e1), (6, e1), (11, e1), (12, e1), (19, e1)],
    [(4, e1), (11, e1), (20, e1)],
    [(1, e1), (3, e1), (4, e1), (6, e1), (9, e1), (12, e1), (13, e1), (14, e1), (21, e1)],
    [(2, e1), (4, e1), (11, e1), (15, e1), (16, e1), (22, e1)],
    [(3, e1), (17, e1), (18, e1), (23, e1)],
    [(4, e1), (20, e1), (24, e1)],
    [(0, e1), (4, e1), (11, e1), (12, e1), (17, e1), (19, e1), (20, e1), (25, e1)]])
private theorem commutator_69_left_s1 : wordMatrix [Atom.root 7 1] = atomMatrix (Atom.root 7 1) := by simp
private theorem commutator_69_left_s0 : wordMatrix [Atom.root 6 1, Atom.root 7 1] = commutator_69_target := by
  rw [wordMatrix_cons, commutator_69_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 6 1))
  decide +kernel
private theorem commutator_69_left : wordMatrix [Atom.root 6 1, Atom.root 7 1] = commutator_69_target := commutator_69_left_s0
private theorem commutator_69_right_s1 : wordMatrix [Atom.root 6 1] = atomMatrix (Atom.root 6 1) := by simp
private theorem commutator_69_right_s0 : wordMatrix [Atom.root 7 1, Atom.root 6 1] = commutator_69_target := by
  rw [wordMatrix_cons, commutator_69_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 7 1))
  decide +kernel
private theorem commutator_69_right : wordMatrix [Atom.root 7 1, Atom.root 6 1] = commutator_69_target := commutator_69_right_s0
theorem commutator_69 : wordGroup (commutator_lhs 69) = wordGroup (commutator_rhs 69) := by
  apply word_eq_of_matrix_eq
  exact commutator_69_left.trans commutator_69_right.symm

private def commutator_70_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(1, e1), (5, e1)],
    [(0, e1), (6, e1)],
    [(0, e1), (2, e1), (7, e1)],
    [(1, e1), (8, e1)],
    [(3, e1), (9, e1)],
    [(0, e1), (10, e1)],
    [(4, e1), (11, e1)],
    [(3, e1), (12, e1)],
    [(6, e1), (13, e1)],
    [(1, e1), (2, e1), (5, e1), (14, e1)],
    [(4, e1), (15, e1)],
    [(0, e1), (2, e1), (6, e1), (7, e1), (16, e1)],
    [(17, e1)],
    [(3, e1), (4, e1), (9, e1), (18, e1)],
    [(0, e1), (3, e1), (6, e1), (9, e1), (12, e1), (19, e1)],
    [(4, e1), (11, e1), (20, e1)],
    [(0, e1), (1, e1), (2, e1), (7, e1), (10, e1), (14, e1), (21, e1)],
    [(2, e1), (3, e1), (6, e1), (13, e1), (16, e1), (22, e1)],
    [(3, e1), (4, e1), (11, e1), (18, e1), (23, e1)],
    [(4, e1), (17, e1), (20, e1), (24, e1)],
    [(0, e1), (3, e1), (4, e1), (9, e1), (12, e1), (15, e1), (18, e1), (19, e1), (25, e1)]])
private theorem commutator_70_left_s1 : wordMatrix [Atom.root 8 1] = atomMatrix (Atom.root 8 1) := by simp
private theorem commutator_70_left_s0 : wordMatrix [Atom.root 6 1, Atom.root 8 1] = commutator_70_target := by
  rw [wordMatrix_cons, commutator_70_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 6 1))
  decide +kernel
private theorem commutator_70_left : wordMatrix [Atom.root 6 1, Atom.root 8 1] = commutator_70_target := commutator_70_left_s0
private theorem commutator_70_right_s1 : wordMatrix [Atom.root 6 1] = atomMatrix (Atom.root 6 1) := by simp
private theorem commutator_70_right_s0 : wordMatrix [Atom.root 8 1, Atom.root 6 1] = commutator_70_target := by
  rw [wordMatrix_cons, commutator_70_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 8 1))
  decide +kernel
private theorem commutator_70_right : wordMatrix [Atom.root 8 1, Atom.root 6 1] = commutator_70_target := commutator_70_right_s0
theorem commutator_70 : wordGroup (commutator_lhs 70) = wordGroup (commutator_rhs 70) := by
  apply word_eq_of_matrix_eq
  exact commutator_70_left.trans commutator_70_right.symm

private def commutator_71_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(1, e1), (5, e1)],
    [(0, e1), (6, e1)],
    [(2, e1), (7, e1)],
    [(8, e1)],
    [(0, e1), (3, e1), (9, e1)],
    [(1, e1), (10, e1)],
    [(4, e1), (11, e1)],
    [(2, e1), (12, e1)],
    [(6, e1), (13, e1)],
    [(1, e1), (5, e1), (14, e1)],
    [(0, e1), (15, e1)],
    [(1, e1), (2, e1), (7, e1), (16, e1)],
    [(4, e1), (17, e1)],
    [(0, e1), (3, e1), (6, e1), (9, e1), (18, e1)],
    [(0, e1), (2, e1), (6, e1), (7, e1), (12, e1), (19, e1)],
    [(3, e1), (4, e1), (11, e1), (20, e1)],
    [(1, e1), (8, e1), (14, e1), (21, e1)],
    [(1, e1), (2, e1), (5, e1), (16, e1), (22, e1)],
    [(2, e1), (3, e1), (6, e1), (13, e1), (18, e1), (23, e1)],
    [(0, e1), (3, e1), (4, e1), (9, e1), (15, e1), (20, e1), (24, e1)],
    [(0, e1), (1, e1), (2, e1), (7, e1), (10, e1), (12, e1), (16, e1), (19, e1), (25, e1)]])
private theorem commutator_71_left_s1 : wordMatrix [Atom.root 9 1] = atomMatrix (Atom.root 9 1) := by simp
private theorem commutator_71_left_s0 : wordMatrix [Atom.root 6 1, Atom.root 9 1] = commutator_71_target := by
  rw [wordMatrix_cons, commutator_71_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 6 1))
  decide +kernel
private theorem commutator_71_left : wordMatrix [Atom.root 6 1, Atom.root 9 1] = commutator_71_target := commutator_71_left_s0
private theorem commutator_71_right_s1 : wordMatrix [Atom.root 6 1] = atomMatrix (Atom.root 6 1) := by simp
private theorem commutator_71_right_s0 : wordMatrix [Atom.root 9 1, Atom.root 6 1] = commutator_71_target := by
  rw [wordMatrix_cons, commutator_71_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 9 1))
  decide +kernel
private theorem commutator_71_right : wordMatrix [Atom.root 9 1, Atom.root 6 1] = commutator_71_target := commutator_71_right_s0
theorem commutator_71 : wordGroup (commutator_lhs 71) = wordGroup (commutator_rhs 71) := by
  apply word_eq_of_matrix_eq
  exact commutator_71_left.trans commutator_71_right.symm

end Kourovka.Problem2153.WilsonModel.RootData.Relations
