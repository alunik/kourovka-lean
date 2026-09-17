import Kourovka.Problem2153.WilsonModel.RootData.Relations.Metadata
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
namespace Kourovka.Problem2153.WilsonModel.RootData.Relations
open Field8 F8
private def weyl_6_target : Mat := Sparse.eval (![[(0, e1)],
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
    [(6, e1), (13, e1)],
    [(1, e1), (5, e1), (14, e1)],
    [(15, e1)],
    [(2, e1), (7, e1), (16, e1)],
    [(17, e1)],
    [(3, e1), (9, e1), (18, e1)],
    [(0, e1), (6, e1), (12, e1), (19, e1)],
    [(4, e1), (11, e1), (20, e1)],
    [(1, e1), (14, e1), (21, e1)],
    [(2, e1), (16, e1), (22, e1)],
    [(3, e1), (18, e1), (23, e1)],
    [(4, e1), (20, e1), (24, e1)],
    [(0, e1), (12, e1), (19, e1), (25, e1)]])
private theorem weyl_6_left_s2 : wordMatrix [Atom.sigma] = atomMatrix (Atom.sigma) := by simp
private def weyl_6_left_m1 : Mat := Sparse.eval (![[(1, e1)],
    [(0, e1)],
    [(2, e1)],
    [(1, e1), (5, e1)],
    [(8, e1)],
    [(3, e1)],
    [(2, e1), (7, e1)],
    [(0, e1), (6, e1)],
    [(4, e1)],
    [(10, e1)],
    [(3, e1), (9, e1)],
    [(1, e1), (5, e1), (14, e1)],
    [(6, e1), (12, e1), (13, e1)],
    [(6, e1), (13, e1)],
    [(4, e1), (11, e1)],
    [(2, e1), (7, e1), (16, e1)],
    [(15, e1)],
    [(1, e1), (14, e1), (21, e1)],
    [(0, e1), (6, e1), (12, e1), (19, e1)],
    [(3, e1), (9, e1), (18, e1)],
    [(2, e1), (16, e1), (22, e1)],
    [(17, e1)],
    [(4, e1), (11, e1), (20, e1)],
    [(3, e1), (18, e1), (23, e1)],
    [(0, e1), (12, e1), (19, e1), (25, e1)],
    [(4, e1), (20, e1), (24, e1)]])
private theorem weyl_6_left_s1 : wordMatrix [Atom.root 4 1, Atom.sigma] = weyl_6_left_m1 := by
  rw [wordMatrix_cons, weyl_6_left_s2]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 4 1))
  decide +kernel
private theorem weyl_6_left_s0 : wordMatrix [Atom.sigma, Atom.root 4 1, Atom.sigma] = weyl_6_target := by
  rw [wordMatrix_cons, weyl_6_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.sigma))
  decide +kernel
private theorem weyl_6_left : wordMatrix [Atom.sigma, Atom.root 4 1, Atom.sigma] = weyl_6_target := weyl_6_left_s0
private theorem weyl_6_right_s0 : wordMatrix [Atom.root 6 1] = atomMatrix (Atom.root 6 1) := by simp
private theorem weyl_6_right : wordMatrix [Atom.root 6 1] = weyl_6_target := by
  rw [weyl_6_right_s0]
  decide +kernel
theorem weyl_6 : wordGroup (weyl_lhs 6) = wordGroup (weyl_rhs 6) := by
  apply word_eq_of_matrix_eq
  exact weyl_6_left.trans weyl_6_right.symm

private def weyl_7_target : Mat := Sparse.eval (![[(0, e1)],
    [(0, e1), (1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(3, e1), (5, e1)],
    [(4, e1), (6, e1)],
    [(4, e1), (7, e1)],
    [(4, e1), (6, e1), (7, e1), (8, e1)],
    [(9, e1)],
    [(9, e1), (10, e1)],
    [(11, e1)],
    [(11, e1), (12, e1)],
    [(13, e1)],
    [(11, e1), (13, e1), (14, e1)],
    [(15, e1)],
    [(15, e1), (16, e1)],
    [(17, e1)],
    [(17, e1), (18, e1)],
    [(17, e1), (19, e1)],
    [(20, e1)],
    [(17, e1), (18, e1), (19, e1), (21, e1)],
    [(20, e1), (22, e1)],
    [(23, e1)],
    [(24, e1)],
    [(24, e1), (25, e1)]])
private theorem weyl_7_left_s2 : wordMatrix [Atom.rho] = atomMatrix (Atom.rho) := by simp
private def weyl_7_left_m1 : Mat := Sparse.eval (![[(0, e1)],
    [(4, e1)],
    [(3, e1)],
    [(2, e1)],
    [(0, e1), (1, e1)],
    [(11, e1)],
    [(4, e1), (6, e1)],
    [(9, e1)],
    [(17, e1)],
    [(4, e1), (7, e1)],
    [(15, e1)],
    [(3, e1), (5, e1)],
    [(11, e1), (12, e1)],
    [(13, e1)],
    [(20, e1)],
    [(9, e1), (10, e1)],
    [(17, e1), (18, e1)],
    [(4, e1), (6, e1), (7, e1), (8, e1)],
    [(15, e1), (16, e1)],
    [(17, e1), (19, e1)],
    [(11, e1), (13, e1), (14, e1)],
    [(24, e1)],
    [(23, e1)],
    [(20, e1), (22, e1)],
    [(17, e1), (18, e1), (19, e1), (21, e1)],
    [(24, e1), (25, e1)]])
private theorem weyl_7_left_s1 : wordMatrix [Atom.root 5 1, Atom.rho] = weyl_7_left_m1 := by
  rw [wordMatrix_cons, weyl_7_left_s2]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 5 1))
  decide +kernel
private theorem weyl_7_left_s0 : wordMatrix [Atom.rho, Atom.root 5 1, Atom.rho] = weyl_7_target := by
  rw [wordMatrix_cons, weyl_7_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.rho))
  decide +kernel
private theorem weyl_7_left : wordMatrix [Atom.rho, Atom.root 5 1, Atom.rho] = weyl_7_target := weyl_7_left_s0
private theorem weyl_7_right_s0 : wordMatrix [Atom.root 0 1] = atomMatrix (Atom.root 0 1) := by simp
private theorem weyl_7_right : wordMatrix [Atom.root 0 1] = weyl_7_target := by
  rw [weyl_7_right_s0]
  decide +kernel
theorem weyl_7 : wordGroup (weyl_lhs 7) = wordGroup (weyl_rhs 7) := by
  apply word_eq_of_matrix_eq
  exact weyl_7_left.trans weyl_7_right.symm

private def weyl_8_target : Mat := Sparse.eval (![[(0, e1)],
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
    [(13, e1)],
    [(2, e1), (14, e1)],
    [(4, e1), (15, e1)],
    [(6, e1), (16, e1)],
    [(17, e1)],
    [(4, e1), (18, e1)],
    [(9, e1), (19, e1)],
    [(20, e1)],
    [(0, e1), (7, e1), (10, e1), (21, e1)],
    [(3, e1), (13, e1), (22, e1)],
    [(11, e1), (23, e1)],
    [(17, e1), (24, e1)],
    [(4, e1), (15, e1), (18, e1), (25, e1)]])
private theorem weyl_8_left_s2 : wordMatrix [Atom.sigma] = atomMatrix (Atom.sigma) := by simp
private def weyl_8_left_m1 : Mat := Sparse.eval (![[(1, e1)],
    [(0, e1)],
    [(2, e1)],
    [(5, e1)],
    [(1, e1), (8, e1)],
    [(3, e1)],
    [(0, e1), (7, e1)],
    [(6, e1)],
    [(4, e1)],
    [(0, e1), (10, e1)],
    [(9, e1)],
    [(2, e1), (14, e1)],
    [(3, e1), (12, e1), (13, e1)],
    [(13, e1)],
    [(11, e1)],
    [(6, e1), (16, e1)],
    [(4, e1), (15, e1)],
    [(0, e1), (7, e1), (10, e1), (21, e1)],
    [(9, e1), (19, e1)],
    [(4, e1), (18, e1)],
    [(3, e1), (13, e1), (22, e1)],
    [(17, e1)],
    [(20, e1)],
    [(11, e1), (23, e1)],
    [(4, e1), (15, e1), (18, e1), (25, e1)],
    [(17, e1), (24, e1)]])
private theorem weyl_8_left_s1 : wordMatrix [Atom.root 5 1, Atom.sigma] = weyl_8_left_m1 := by
  rw [wordMatrix_cons, weyl_8_left_s2]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 5 1))
  decide +kernel
private theorem weyl_8_left_s0 : wordMatrix [Atom.sigma, Atom.root 5 1, Atom.sigma] = weyl_8_target := by
  rw [wordMatrix_cons, weyl_8_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.sigma))
  decide +kernel
private theorem weyl_8_left : wordMatrix [Atom.sigma, Atom.root 5 1, Atom.sigma] = weyl_8_target := weyl_8_left_s0
private theorem weyl_8_right_s0 : wordMatrix [Atom.root 8 1] = atomMatrix (Atom.root 8 1) := by simp
private theorem weyl_8_right : wordMatrix [Atom.root 8 1] = weyl_8_target := by
  rw [weyl_8_right_s0]
  decide +kernel
theorem weyl_8 : wordGroup (weyl_lhs 8) = wordGroup (weyl_rhs 8) := by
  apply word_eq_of_matrix_eq
  exact weyl_8_left.trans weyl_8_right.symm

private def weyl_9_target : Mat := Sparse.eval (![[(0, e1)],
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
    [(6, e1), (13, e1)],
    [(1, e1), (5, e1), (14, e1)],
    [(15, e1)],
    [(2, e1), (7, e1), (16, e1)],
    [(17, e1)],
    [(3, e1), (9, e1), (18, e1)],
    [(0, e1), (6, e1), (12, e1), (19, e1)],
    [(4, e1), (11, e1), (20, e1)],
    [(1, e1), (14, e1), (21, e1)],
    [(2, e1), (16, e1), (22, e1)],
    [(3, e1), (18, e1), (23, e1)],
    [(4, e1), (20, e1), (24, e1)],
    [(0, e1), (12, e1), (19, e1), (25, e1)]])
private theorem weyl_9_left_s2 : wordMatrix [Atom.rho] = atomMatrix (Atom.rho) := by simp
private def weyl_9_left_m1 : Mat := Sparse.eval (![[(0, e1)],
    [(4, e1)],
    [(3, e1)],
    [(2, e1)],
    [(1, e1)],
    [(4, e1), (11, e1)],
    [(0, e1), (6, e1)],
    [(3, e1), (9, e1)],
    [(17, e1)],
    [(2, e1), (7, e1)],
    [(15, e1)],
    [(1, e1), (5, e1)],
    [(12, e1)],
    [(6, e1), (13, e1)],
    [(4, e1), (11, e1), (20, e1)],
    [(10, e1)],
    [(3, e1), (9, e1), (18, e1)],
    [(8, e1)],
    [(2, e1), (7, e1), (16, e1)],
    [(0, e1), (6, e1), (12, e1), (19, e1)],
    [(1, e1), (5, e1), (14, e1)],
    [(4, e1), (20, e1), (24, e1)],
    [(3, e1), (18, e1), (23, e1)],
    [(2, e1), (16, e1), (22, e1)],
    [(1, e1), (14, e1), (21, e1)],
    [(0, e1), (12, e1), (19, e1), (25, e1)]])
private theorem weyl_9_left_s1 : wordMatrix [Atom.root 6 1, Atom.rho] = weyl_9_left_m1 := by
  rw [wordMatrix_cons, weyl_9_left_s2]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 6 1))
  decide +kernel
private theorem weyl_9_left_s0 : wordMatrix [Atom.rho, Atom.root 6 1, Atom.rho] = weyl_9_target := by
  rw [wordMatrix_cons, weyl_9_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.rho))
  decide +kernel
private theorem weyl_9_left : wordMatrix [Atom.rho, Atom.root 6 1, Atom.rho] = weyl_9_target := weyl_9_left_s0
private theorem weyl_9_right_s0 : wordMatrix [Atom.root 6 1] = atomMatrix (Atom.root 6 1) := by simp
private theorem weyl_9_right : wordMatrix [Atom.root 6 1] = weyl_9_target := by
  rw [weyl_9_right_s0]
  decide +kernel
theorem weyl_9 : wordGroup (weyl_lhs 9) = wordGroup (weyl_rhs 9) := by
  apply word_eq_of_matrix_eq
  exact weyl_9_left.trans weyl_9_right.symm

private def weyl_10_target : Mat := Sparse.eval (![[(0, e1)],
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
    [(7, e1), (13, e1)],
    [(8, e1), (14, e1)],
    [(2, e1), (6, e1), (15, e1)],
    [(16, e1)],
    [(0, e1), (11, e1), (17, e1)],
    [(1, e1), (7, e1), (12, e1), (13, e1), (18, e1)],
    [(5, e1), (10, e1), (19, e1)],
    [(2, e1), (15, e1), (20, e1)],
    [(21, e1)],
    [(8, e1), (14, e1), (22, e1)],
    [(5, e1), (19, e1), (23, e1)],
    [(1, e1), (12, e1), (13, e1), (18, e1), (24, e1)],
    [(8, e1), (22, e1), (25, e1)]])
private theorem weyl_10_left_s2 : wordMatrix [Atom.sigma] = atomMatrix (Atom.sigma) := by simp
private def weyl_10_left_m1 : Mat := Sparse.eval (![[(1, e1)],
    [(0, e1)],
    [(2, e1)],
    [(5, e1)],
    [(8, e1)],
    [(0, e1), (3, e1)],
    [(1, e1), (7, e1)],
    [(2, e1), (6, e1)],
    [(4, e1)],
    [(5, e1), (10, e1)],
    [(9, e1)],
    [(8, e1), (14, e1)],
    [(12, e1), (13, e1)],
    [(7, e1), (13, e1)],
    [(0, e1), (3, e1), (11, e1)],
    [(16, e1)],
    [(2, e1), (6, e1), (15, e1)],
    [(21, e1)],
    [(5, e1), (10, e1), (19, e1)],
    [(1, e1), (7, e1), (12, e1), (13, e1), (18, e1)],
    [(8, e1), (14, e1), (22, e1)],
    [(0, e1), (11, e1), (17, e1)],
    [(2, e1), (15, e1), (20, e1)],
    [(5, e1), (19, e1), (23, e1)],
    [(8, e1), (22, e1), (25, e1)],
    [(1, e1), (12, e1), (13, e1), (18, e1), (24, e1)]])
private theorem weyl_10_left_s1 : wordMatrix [Atom.root 6 1, Atom.sigma] = weyl_10_left_m1 := by
  rw [wordMatrix_cons, weyl_10_left_s2]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 6 1))
  decide +kernel
private theorem weyl_10_left_s0 : wordMatrix [Atom.sigma, Atom.root 6 1, Atom.sigma] = weyl_10_target := by
  rw [wordMatrix_cons, weyl_10_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.sigma))
  decide +kernel
private theorem weyl_10_left : wordMatrix [Atom.sigma, Atom.root 6 1, Atom.sigma] = weyl_10_target := weyl_10_left_s0
private theorem weyl_10_right_s0 : wordMatrix [Atom.root 4 1] = atomMatrix (Atom.root 4 1) := by simp
private theorem weyl_10_right : wordMatrix [Atom.root 4 1] = weyl_10_target := by
  rw [weyl_10_right_s0]
  decide +kernel
theorem weyl_10 : wordGroup (weyl_lhs 10) = wordGroup (weyl_rhs 10) := by
  apply word_eq_of_matrix_eq
  exact weyl_10_left.trans weyl_10_right.symm

private def weyl_11_target : Mat := Sparse.eval (![[(0, e1)],
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
    [(1, e1), (13, e1)],
    [(14, e1)],
    [(2, e1), (15, e1)],
    [(16, e1)],
    [(0, e1), (3, e1), (17, e1)],
    [(1, e1), (18, e1)],
    [(5, e1), (19, e1)],
    [(2, e1), (6, e1), (20, e1)],
    [(21, e1)],
    [(8, e1), (22, e1)],
    [(5, e1), (10, e1), (23, e1)],
    [(1, e1), (7, e1), (12, e1), (13, e1), (24, e1)],
    [(8, e1), (14, e1), (25, e1)]])
private theorem weyl_11_left_s2 : wordMatrix [Atom.rho] = atomMatrix (Atom.rho) := by simp
private def weyl_11_left_m1 : Mat := Sparse.eval (![[(0, e1)],
    [(4, e1)],
    [(3, e1)],
    [(2, e1)],
    [(1, e1)],
    [(0, e1), (11, e1)],
    [(6, e1)],
    [(9, e1)],
    [(0, e1), (3, e1), (17, e1)],
    [(7, e1)],
    [(2, e1), (15, e1)],
    [(5, e1)],
    [(1, e1), (12, e1)],
    [(1, e1), (13, e1)],
    [(2, e1), (6, e1), (20, e1)],
    [(10, e1)],
    [(1, e1), (18, e1)],
    [(8, e1)],
    [(16, e1)],
    [(5, e1), (19, e1)],
    [(14, e1)],
    [(1, e1), (7, e1), (12, e1), (13, e1), (24, e1)],
    [(5, e1), (10, e1), (23, e1)],
    [(8, e1), (22, e1)],
    [(21, e1)],
    [(8, e1), (14, e1), (25, e1)]])
private theorem weyl_11_left_s1 : wordMatrix [Atom.root 7 1, Atom.rho] = weyl_11_left_m1 := by
  rw [wordMatrix_cons, weyl_11_left_s2]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 7 1))
  decide +kernel
private theorem weyl_11_left_s0 : wordMatrix [Atom.rho, Atom.root 7 1, Atom.rho] = weyl_11_target := by
  rw [wordMatrix_cons, weyl_11_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.rho))
  decide +kernel
private theorem weyl_11_left : wordMatrix [Atom.rho, Atom.root 7 1, Atom.rho] = weyl_11_target := weyl_11_left_s0
private theorem weyl_11_right_s0 : wordMatrix [Atom.root 10 1] = atomMatrix (Atom.root 10 1) := by simp
private theorem weyl_11_right : wordMatrix [Atom.root 10 1] = weyl_11_target := by
  rw [weyl_11_right_s0]
  decide +kernel
theorem weyl_11 : wordGroup (weyl_lhs 11) = wordGroup (weyl_rhs 11) := by
  apply word_eq_of_matrix_eq
  exact weyl_11_left.trans weyl_11_right.symm

end Kourovka.Problem2153.WilsonModel.RootData.Relations
