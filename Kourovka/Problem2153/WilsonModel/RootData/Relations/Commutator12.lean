import Kourovka.Problem2153.WilsonModel.RootData.Relations.Metadata
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
namespace Kourovka.Problem2153.WilsonModel.RootData.Relations
open Field8 F8
private def commutator_72_target : Mat := Sparse.eval (![[(0, e1)],
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
    [(0, e1), (4, e1), (11, e1)],
    [(1, e1), (12, e1)],
    [(1, e1), (6, e1), (13, e1)],
    [(1, e1), (5, e1), (14, e1)],
    [(2, e1), (15, e1)],
    [(2, e1), (7, e1), (16, e1)],
    [(0, e1), (3, e1), (17, e1)],
    [(1, e1), (3, e1), (9, e1), (18, e1)],
    [(0, e1), (1, e1), (5, e1), (6, e1), (12, e1), (19, e1)],
    [(0, e1), (2, e1), (4, e1), (6, e1), (11, e1), (20, e1)],
    [(1, e1), (14, e1), (21, e1)],
    [(2, e1), (8, e1), (16, e1), (22, e1)],
    [(1, e1), (3, e1), (5, e1), (10, e1), (18, e1), (23, e1)],
    [(1, e1), (2, e1), (4, e1), (6, e1), (7, e1), (12, e1), (13, e1), (20, e1), (24, e1)],
    [(0, e1), (1, e1), (5, e1), (8, e1), (12, e1), (14, e1), (19, e1), (25, e1)]])
private theorem commutator_72_left_s1 : wordMatrix [Atom.root 10 1] = atomMatrix (Atom.root 10 1) := by simp
private theorem commutator_72_left_s0 : wordMatrix [Atom.root 6 1, Atom.root 10 1] = commutator_72_target := by
  rw [wordMatrix_cons, commutator_72_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 6 1))
  decide +kernel
private theorem commutator_72_left : wordMatrix [Atom.root 6 1, Atom.root 10 1] = commutator_72_target := commutator_72_left_s0
private theorem commutator_72_right_s1 : wordMatrix [Atom.root 6 1] = atomMatrix (Atom.root 6 1) := by simp
private theorem commutator_72_right_s0 : wordMatrix [Atom.root 10 1, Atom.root 6 1] = commutator_72_target := by
  rw [wordMatrix_cons, commutator_72_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 10 1))
  decide +kernel
private theorem commutator_72_right : wordMatrix [Atom.root 10 1, Atom.root 6 1] = commutator_72_target := commutator_72_right_s0
theorem commutator_72 : wordGroup (commutator_lhs 72) = wordGroup (commutator_rhs 72) := by
  apply word_eq_of_matrix_eq
  exact commutator_72_left.trans commutator_72_right.symm

private def commutator_73_target : Mat := Sparse.eval (![[(0, e1)],
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
    [(0, e1), (6, e1), (13, e1)],
    [(5, e1), (14, e1)],
    [(15, e1)],
    [(7, e1), (16, e1)],
    [(17, e1)],
    [(9, e1), (18, e1)],
    [(6, e1), (12, e1), (19, e1)],
    [(11, e1), (20, e1)],
    [(1, e1), (5, e1), (14, e1), (21, e1)],
    [(2, e1), (7, e1), (16, e1), (22, e1)],
    [(3, e1), (9, e1), (18, e1), (23, e1)],
    [(4, e1), (11, e1), (20, e1), (24, e1)],
    [(0, e1), (6, e1), (19, e1), (25, e1)]])
private theorem commutator_73_left_s1 : wordMatrix [Atom.root 11 1] = atomMatrix (Atom.root 11 1) := by simp
private theorem commutator_73_left_s0 : wordMatrix [Atom.root 6 1, Atom.root 11 1] = commutator_73_target := by
  rw [wordMatrix_cons, commutator_73_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 6 1))
  decide +kernel
private theorem commutator_73_left : wordMatrix [Atom.root 6 1, Atom.root 11 1] = commutator_73_target := commutator_73_left_s0
private theorem commutator_73_right_s1 : wordMatrix [Atom.root 6 1] = atomMatrix (Atom.root 6 1) := by simp
private theorem commutator_73_right_s0 : wordMatrix [Atom.root 11 1, Atom.root 6 1] = commutator_73_target := by
  rw [wordMatrix_cons, commutator_73_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 11 1))
  decide +kernel
private theorem commutator_73_right : wordMatrix [Atom.root 11 1, Atom.root 6 1] = commutator_73_target := commutator_73_right_s0
theorem commutator_73 : wordGroup (commutator_lhs 73) = wordGroup (commutator_rhs 73) := by
  apply word_eq_of_matrix_eq
  exact commutator_73_left.trans commutator_73_right.symm

private def commutator_74_target : Mat := Sparse.eval (![[(0, e1)],
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
    [(0, e2), (6, e1), (13, e1)],
    [(1, e3), (5, e1), (14, e1)],
    [(15, e1)],
    [(2, e3), (7, e1), (16, e1)],
    [(17, e1)],
    [(3, e3), (9, e1), (18, e1)],
    [(0, e7), (6, e1), (12, e1), (19, e1)],
    [(4, e3), (11, e1), (20, e1)],
    [(1, e5), (5, e2), (14, e1), (21, e1)],
    [(2, e5), (7, e2), (16, e1), (22, e1)],
    [(3, e5), (9, e2), (18, e1), (23, e1)],
    [(4, e5), (11, e2), (20, e1), (24, e1)],
    [(0, e3), (6, e6), (12, e3), (19, e1), (25, e1)]])
private theorem commutator_74_left_s1 : wordMatrix [Atom.root 11 2] = atomMatrix (Atom.root 11 2) := by simp
private theorem commutator_74_left_s0 : wordMatrix [Atom.root 6 1, Atom.root 11 2] = commutator_74_target := by
  rw [wordMatrix_cons, commutator_74_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 6 1))
  decide +kernel
private theorem commutator_74_left : wordMatrix [Atom.root 6 1, Atom.root 11 2] = commutator_74_target := commutator_74_left_s0
private theorem commutator_74_right_s1 : wordMatrix [Atom.root 6 1] = atomMatrix (Atom.root 6 1) := by simp
private theorem commutator_74_right_s0 : wordMatrix [Atom.root 11 2, Atom.root 6 1] = commutator_74_target := by
  rw [wordMatrix_cons, commutator_74_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 11 2))
  decide +kernel
private theorem commutator_74_right : wordMatrix [Atom.root 11 2, Atom.root 6 1] = commutator_74_target := commutator_74_right_s0
theorem commutator_74 : wordGroup (commutator_lhs 74) = wordGroup (commutator_rhs 74) := by
  apply word_eq_of_matrix_eq
  exact commutator_74_left.trans commutator_74_right.symm

private def commutator_75_target : Mat := Sparse.eval (![[(0, e1)],
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
    [(0, e3), (6, e1), (13, e1)],
    [(1, e2), (5, e1), (14, e1)],
    [(15, e1)],
    [(2, e2), (7, e1), (16, e1)],
    [(17, e1)],
    [(3, e2), (9, e1), (18, e1)],
    [(0, e6), (6, e1), (12, e1), (19, e1)],
    [(4, e2), (11, e1), (20, e1)],
    [(1, e5), (5, e3), (14, e1), (21, e1)],
    [(2, e5), (7, e3), (16, e1), (22, e1)],
    [(3, e5), (9, e3), (18, e1), (23, e1)],
    [(4, e5), (11, e3), (20, e1), (24, e1)],
    [(0, e3), (6, e7), (12, e2), (19, e1), (25, e1)]])
private theorem commutator_75_left_s1 : wordMatrix [Atom.root 11 3] = atomMatrix (Atom.root 11 3) := by simp
private theorem commutator_75_left_s0 : wordMatrix [Atom.root 6 1, Atom.root 11 3] = commutator_75_target := by
  rw [wordMatrix_cons, commutator_75_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 6 1))
  decide +kernel
private theorem commutator_75_left : wordMatrix [Atom.root 6 1, Atom.root 11 3] = commutator_75_target := commutator_75_left_s0
private theorem commutator_75_right_s1 : wordMatrix [Atom.root 6 1] = atomMatrix (Atom.root 6 1) := by simp
private theorem commutator_75_right_s0 : wordMatrix [Atom.root 11 3, Atom.root 6 1] = commutator_75_target := by
  rw [wordMatrix_cons, commutator_75_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 11 3))
  decide +kernel
private theorem commutator_75_right : wordMatrix [Atom.root 11 3, Atom.root 6 1] = commutator_75_target := commutator_75_right_s0
theorem commutator_75 : wordGroup (commutator_lhs 75) = wordGroup (commutator_rhs 75) := by
  apply word_eq_of_matrix_eq
  exact commutator_75_left.trans commutator_75_right.symm

private def commutator_76_target : Mat := Sparse.eval (![[(0, e1)],
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
    [(0, e4), (6, e1), (13, e1)],
    [(1, e5), (5, e1), (14, e1)],
    [(15, e1)],
    [(2, e5), (7, e1), (16, e1)],
    [(17, e1)],
    [(3, e5), (9, e1), (18, e1)],
    [(0, e3), (6, e1), (12, e1), (19, e1)],
    [(4, e5), (11, e1), (20, e1)],
    [(1, e7), (5, e4), (14, e1), (21, e1)],
    [(2, e7), (7, e4), (16, e1), (22, e1)],
    [(3, e7), (9, e4), (18, e1), (23, e1)],
    [(4, e7), (11, e4), (20, e1), (24, e1)],
    [(0, e5), (6, e2), (12, e5), (19, e1), (25, e1)]])
private theorem commutator_76_left_s1 : wordMatrix [Atom.root 11 4] = atomMatrix (Atom.root 11 4) := by simp
private theorem commutator_76_left_s0 : wordMatrix [Atom.root 6 1, Atom.root 11 4] = commutator_76_target := by
  rw [wordMatrix_cons, commutator_76_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 6 1))
  decide +kernel
private theorem commutator_76_left : wordMatrix [Atom.root 6 1, Atom.root 11 4] = commutator_76_target := commutator_76_left_s0
private theorem commutator_76_right_s1 : wordMatrix [Atom.root 6 1] = atomMatrix (Atom.root 6 1) := by simp
private theorem commutator_76_right_s0 : wordMatrix [Atom.root 11 4, Atom.root 6 1] = commutator_76_target := by
  rw [wordMatrix_cons, commutator_76_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 11 4))
  decide +kernel
private theorem commutator_76_right : wordMatrix [Atom.root 11 4, Atom.root 6 1] = commutator_76_target := commutator_76_right_s0
theorem commutator_76 : wordGroup (commutator_lhs 76) = wordGroup (commutator_rhs 76) := by
  apply word_eq_of_matrix_eq
  exact commutator_76_left.trans commutator_76_right.symm

private def commutator_77_target : Mat := Sparse.eval (![[(0, e1)],
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
    [(0, e5), (6, e1), (13, e1)],
    [(1, e4), (5, e1), (14, e1)],
    [(15, e1)],
    [(2, e4), (7, e1), (16, e1)],
    [(17, e1)],
    [(3, e4), (9, e1), (18, e1)],
    [(0, e2), (6, e1), (12, e1), (19, e1)],
    [(4, e4), (11, e1), (20, e1)],
    [(1, e7), (5, e5), (14, e1), (21, e1)],
    [(2, e7), (7, e5), (16, e1), (22, e1)],
    [(3, e7), (9, e5), (18, e1), (23, e1)],
    [(4, e7), (11, e5), (20, e1), (24, e1)],
    [(0, e5), (6, e3), (12, e4), (19, e1), (25, e1)]])
private theorem commutator_77_left_s1 : wordMatrix [Atom.root 11 5] = atomMatrix (Atom.root 11 5) := by simp
private theorem commutator_77_left_s0 : wordMatrix [Atom.root 6 1, Atom.root 11 5] = commutator_77_target := by
  rw [wordMatrix_cons, commutator_77_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 6 1))
  decide +kernel
private theorem commutator_77_left : wordMatrix [Atom.root 6 1, Atom.root 11 5] = commutator_77_target := commutator_77_left_s0
private theorem commutator_77_right_s1 : wordMatrix [Atom.root 6 1] = atomMatrix (Atom.root 6 1) := by simp
private theorem commutator_77_right_s0 : wordMatrix [Atom.root 11 5, Atom.root 6 1] = commutator_77_target := by
  rw [wordMatrix_cons, commutator_77_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 11 5))
  decide +kernel
private theorem commutator_77_right : wordMatrix [Atom.root 11 5, Atom.root 6 1] = commutator_77_target := commutator_77_right_s0
theorem commutator_77 : wordGroup (commutator_lhs 77) = wordGroup (commutator_rhs 77) := by
  apply word_eq_of_matrix_eq
  exact commutator_77_left.trans commutator_77_right.symm

end Kourovka.Problem2153.WilsonModel.RootData.Relations
