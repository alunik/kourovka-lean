import Kourovka.Problem2153.WilsonModel.RootData.Relations.Metadata
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
namespace Kourovka.Problem2153.WilsonModel.RootData.Relations
open Field8 F8
private def weyl_12_target : Mat := Sparse.eval (![[(0, e1)],
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
    [(8, e1), (13, e1)],
    [(14, e1)],
    [(8, e1), (15, e1)],
    [(16, e1)],
    [(8, e1), (10, e1), (12, e1), (17, e1)],
    [(14, e1), (18, e1)],
    [(19, e1)],
    [(14, e1), (16, e1), (20, e1)],
    [(21, e1)],
    [(22, e1)],
    [(21, e1), (23, e1)],
    [(21, e1), (22, e1), (24, e1)],
    [(25, e1)]])
private theorem weyl_12_left_s2 : wordMatrix [Atom.sigma] = atomMatrix (Atom.sigma) := by simp
private def weyl_12_left_m1 : Mat := Sparse.eval (![[(1, e1)],
    [(0, e1)],
    [(2, e1)],
    [(5, e1)],
    [(8, e1)],
    [(1, e1), (3, e1)],
    [(7, e1)],
    [(6, e1)],
    [(1, e1), (2, e1), (4, e1)],
    [(10, e1)],
    [(5, e1), (9, e1)],
    [(14, e1)],
    [(8, e1), (12, e1), (13, e1)],
    [(8, e1), (13, e1)],
    [(5, e1), (7, e1), (11, e1)],
    [(16, e1)],
    [(8, e1), (15, e1)],
    [(21, e1)],
    [(19, e1)],
    [(14, e1), (18, e1)],
    [(22, e1)],
    [(8, e1), (10, e1), (12, e1), (17, e1)],
    [(14, e1), (16, e1), (20, e1)],
    [(21, e1), (23, e1)],
    [(25, e1)],
    [(21, e1), (22, e1), (24, e1)]])
private theorem weyl_12_left_s1 : wordMatrix [Atom.root 7 1, Atom.sigma] = weyl_12_left_m1 := by
  rw [wordMatrix_cons, weyl_12_left_s2]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 7 1))
  decide +kernel
private theorem weyl_12_left_s0 : wordMatrix [Atom.sigma, Atom.root 7 1, Atom.sigma] = weyl_12_target := by
  rw [wordMatrix_cons, weyl_12_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.sigma))
  decide +kernel
private theorem weyl_12_left : wordMatrix [Atom.sigma, Atom.root 7 1, Atom.sigma] = weyl_12_target := weyl_12_left_s0
private theorem weyl_12_right_s0 : wordMatrix [Atom.root 3 1] = atomMatrix (Atom.root 3 1) := by simp
private theorem weyl_12_right : wordMatrix [Atom.root 3 1] = weyl_12_target := by
  rw [weyl_12_right_s0]
  decide +kernel
theorem weyl_12 : wordGroup (weyl_lhs 12) = wordGroup (weyl_rhs 12) := by
  apply word_eq_of_matrix_eq
  exact weyl_12_left.trans weyl_12_right.symm

private def weyl_13_target : Mat := Sparse.eval (![[(0, e1)],
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
    [(13, e1)],
    [(14, e1)],
    [(0, e1), (15, e1)],
    [(1, e1), (16, e1)],
    [(4, e1), (17, e1)],
    [(6, e1), (18, e1)],
    [(7, e1), (19, e1)],
    [(3, e1), (20, e1)],
    [(8, e1), (21, e1)],
    [(5, e1), (22, e1)],
    [(2, e1), (13, e1), (23, e1)],
    [(0, e1), (9, e1), (15, e1), (24, e1)],
    [(1, e1), (10, e1), (16, e1), (25, e1)]])
private theorem weyl_13_left_s2 : wordMatrix [Atom.rho] = atomMatrix (Atom.rho) := by simp
private def weyl_13_left_m1 : Mat := Sparse.eval (![[(0, e1)],
    [(4, e1)],
    [(3, e1)],
    [(2, e1)],
    [(1, e1)],
    [(11, e1)],
    [(6, e1)],
    [(0, e1), (9, e1)],
    [(4, e1), (17, e1)],
    [(7, e1)],
    [(0, e1), (15, e1)],
    [(5, e1)],
    [(2, e1), (12, e1)],
    [(13, e1)],
    [(3, e1), (20, e1)],
    [(1, e1), (10, e1)],
    [(6, e1), (18, e1)],
    [(8, e1)],
    [(1, e1), (16, e1)],
    [(7, e1), (19, e1)],
    [(14, e1)],
    [(0, e1), (9, e1), (15, e1), (24, e1)],
    [(2, e1), (13, e1), (23, e1)],
    [(5, e1), (22, e1)],
    [(8, e1), (21, e1)],
    [(1, e1), (10, e1), (16, e1), (25, e1)]])
private theorem weyl_13_left_s1 : wordMatrix [Atom.root 8 1, Atom.rho] = weyl_13_left_m1 := by
  rw [wordMatrix_cons, weyl_13_left_s2]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 8 1))
  decide +kernel
private theorem weyl_13_left_s0 : wordMatrix [Atom.rho, Atom.root 8 1, Atom.rho] = weyl_13_target := by
  rw [wordMatrix_cons, weyl_13_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.rho))
  decide +kernel
private theorem weyl_13_left : wordMatrix [Atom.rho, Atom.root 8 1, Atom.rho] = weyl_13_target := weyl_13_left_s0
private theorem weyl_13_right_s0 : wordMatrix [Atom.root 9 1] = atomMatrix (Atom.root 9 1) := by simp
private theorem weyl_13_right : wordMatrix [Atom.root 9 1] = weyl_13_target := by
  rw [weyl_13_right_s0]
  decide +kernel
theorem weyl_13 : wordGroup (weyl_lhs 13) = wordGroup (weyl_rhs 13) := by
  apply word_eq_of_matrix_eq
  exact weyl_13_left.trans weyl_13_right.symm

private def weyl_14_target : Mat := Sparse.eval (![[(0, e1)],
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
    [(13, e1)],
    [(14, e1)],
    [(7, e1), (15, e1)],
    [(8, e1), (16, e1)],
    [(1, e1), (6, e1), (9, e1), (17, e1)],
    [(10, e1), (18, e1)],
    [(8, e1), (19, e1)],
    [(5, e1), (13, e1), (20, e1)],
    [(21, e1)],
    [(22, e1)],
    [(14, e1), (23, e1)],
    [(8, e1), (16, e1), (19, e1), (24, e1)],
    [(21, e1), (25, e1)]])
private theorem weyl_14_left_s2 : wordMatrix [Atom.sigma] = atomMatrix (Atom.sigma) := by simp
private def weyl_14_left_m1 : Mat := Sparse.eval (![[(1, e1)],
    [(0, e1)],
    [(2, e1)],
    [(5, e1)],
    [(8, e1)],
    [(3, e1)],
    [(7, e1)],
    [(1, e1), (6, e1)],
    [(0, e1), (4, e1)],
    [(10, e1)],
    [(1, e1), (9, e1)],
    [(14, e1)],
    [(5, e1), (12, e1), (13, e1)],
    [(13, e1)],
    [(2, e1), (11, e1)],
    [(8, e1), (16, e1)],
    [(7, e1), (15, e1)],
    [(21, e1)],
    [(8, e1), (19, e1)],
    [(10, e1), (18, e1)],
    [(22, e1)],
    [(1, e1), (6, e1), (9, e1), (17, e1)],
    [(5, e1), (13, e1), (20, e1)],
    [(14, e1), (23, e1)],
    [(21, e1), (25, e1)],
    [(8, e1), (16, e1), (19, e1), (24, e1)]])
private theorem weyl_14_left_s1 : wordMatrix [Atom.root 8 1, Atom.sigma] = weyl_14_left_m1 := by
  rw [wordMatrix_cons, weyl_14_left_s2]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 8 1))
  decide +kernel
private theorem weyl_14_left_s0 : wordMatrix [Atom.sigma, Atom.root 8 1, Atom.sigma] = weyl_14_target := by
  rw [wordMatrix_cons, weyl_14_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.sigma))
  decide +kernel
private theorem weyl_14_left : wordMatrix [Atom.sigma, Atom.root 8 1, Atom.sigma] = weyl_14_target := weyl_14_left_s0
private theorem weyl_14_right_s0 : wordMatrix [Atom.root 5 1] = atomMatrix (Atom.root 5 1) := by simp
private theorem weyl_14_right : wordMatrix [Atom.root 5 1] = weyl_14_target := by
  rw [weyl_14_right_s0]
  decide +kernel
theorem weyl_14 : wordGroup (weyl_lhs 14) = wordGroup (weyl_rhs 14) := by
  apply word_eq_of_matrix_eq
  exact weyl_14_left.trans weyl_14_right.symm

private def weyl_15_target : Mat := Sparse.eval (![[(0, e1)],
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
private theorem weyl_15_left_s2 : wordMatrix [Atom.rho] = atomMatrix (Atom.rho) := by simp
private def weyl_15_left_m1 : Mat := Sparse.eval (![[(0, e1)],
    [(4, e1)],
    [(3, e1)],
    [(2, e1)],
    [(1, e1)],
    [(11, e1)],
    [(6, e1)],
    [(9, e1)],
    [(17, e1)],
    [(0, e1), (7, e1)],
    [(4, e1), (15, e1)],
    [(5, e1)],
    [(3, e1), (12, e1)],
    [(13, e1)],
    [(20, e1)],
    [(0, e1), (10, e1)],
    [(4, e1), (18, e1)],
    [(1, e1), (8, e1)],
    [(6, e1), (16, e1)],
    [(9, e1), (19, e1)],
    [(2, e1), (14, e1)],
    [(17, e1), (24, e1)],
    [(11, e1), (23, e1)],
    [(3, e1), (13, e1), (22, e1)],
    [(0, e1), (7, e1), (10, e1), (21, e1)],
    [(4, e1), (15, e1), (18, e1), (25, e1)]])
private theorem weyl_15_left_s1 : wordMatrix [Atom.root 9 1, Atom.rho] = weyl_15_left_m1 := by
  rw [wordMatrix_cons, weyl_15_left_s2]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 9 1))
  decide +kernel
private theorem weyl_15_left_s0 : wordMatrix [Atom.rho, Atom.root 9 1, Atom.rho] = weyl_15_target := by
  rw [wordMatrix_cons, weyl_15_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.rho))
  decide +kernel
private theorem weyl_15_left : wordMatrix [Atom.rho, Atom.root 9 1, Atom.rho] = weyl_15_target := weyl_15_left_s0
private theorem weyl_15_right_s0 : wordMatrix [Atom.root 8 1] = atomMatrix (Atom.root 8 1) := by simp
private theorem weyl_15_right : wordMatrix [Atom.root 8 1] = weyl_15_target := by
  rw [weyl_15_right_s0]
  decide +kernel
theorem weyl_15 : wordGroup (weyl_lhs 15) = wordGroup (weyl_rhs 15) := by
  apply word_eq_of_matrix_eq
  exact weyl_15_left.trans weyl_15_right.symm

private def weyl_16_target : Mat := Sparse.eval (![[(0, e1)],
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
    [(13, e1)],
    [(14, e1)],
    [(0, e1), (15, e1)],
    [(1, e1), (16, e1)],
    [(4, e1), (17, e1)],
    [(6, e1), (18, e1)],
    [(7, e1), (19, e1)],
    [(3, e1), (20, e1)],
    [(8, e1), (21, e1)],
    [(5, e1), (22, e1)],
    [(2, e1), (13, e1), (23, e1)],
    [(0, e1), (9, e1), (15, e1), (24, e1)],
    [(1, e1), (10, e1), (16, e1), (25, e1)]])
private theorem weyl_16_left_s2 : wordMatrix [Atom.sigma] = atomMatrix (Atom.sigma) := by simp
private def weyl_16_left_m1 : Mat := Sparse.eval (![[(1, e1)],
    [(0, e1)],
    [(2, e1)],
    [(5, e1)],
    [(8, e1)],
    [(3, e1)],
    [(7, e1)],
    [(6, e1)],
    [(4, e1)],
    [(1, e1), (10, e1)],
    [(0, e1), (9, e1)],
    [(14, e1)],
    [(2, e1), (12, e1), (13, e1)],
    [(13, e1)],
    [(11, e1)],
    [(1, e1), (16, e1)],
    [(0, e1), (15, e1)],
    [(8, e1), (21, e1)],
    [(7, e1), (19, e1)],
    [(6, e1), (18, e1)],
    [(5, e1), (22, e1)],
    [(4, e1), (17, e1)],
    [(3, e1), (20, e1)],
    [(2, e1), (13, e1), (23, e1)],
    [(1, e1), (10, e1), (16, e1), (25, e1)],
    [(0, e1), (9, e1), (15, e1), (24, e1)]])
private theorem weyl_16_left_s1 : wordMatrix [Atom.root 9 1, Atom.sigma] = weyl_16_left_m1 := by
  rw [wordMatrix_cons, weyl_16_left_s2]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 9 1))
  decide +kernel
private theorem weyl_16_left_s0 : wordMatrix [Atom.sigma, Atom.root 9 1, Atom.sigma] = weyl_16_target := by
  rw [wordMatrix_cons, weyl_16_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.sigma))
  decide +kernel
private theorem weyl_16_left : wordMatrix [Atom.sigma, Atom.root 9 1, Atom.sigma] = weyl_16_target := weyl_16_left_s0
private theorem weyl_16_right_s0 : wordMatrix [Atom.root 9 1] = atomMatrix (Atom.root 9 1) := by simp
private theorem weyl_16_right : wordMatrix [Atom.root 9 1] = weyl_16_target := by
  rw [weyl_16_right_s0]
  decide +kernel
theorem weyl_16 : wordGroup (weyl_lhs 16) = wordGroup (weyl_rhs 16) := by
  apply word_eq_of_matrix_eq
  exact weyl_16_left.trans weyl_16_right.symm

private def weyl_17_target : Mat := Sparse.eval (![[(0, e1)],
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
    [(4, e1), (13, e1)],
    [(3, e1), (6, e1), (14, e1)],
    [(15, e1)],
    [(4, e1), (16, e1)],
    [(17, e1)],
    [(18, e1)],
    [(11, e1), (19, e1)],
    [(20, e1)],
    [(4, e1), (9, e1), (12, e1), (13, e1), (21, e1)],
    [(11, e1), (15, e1), (22, e1)],
    [(17, e1), (23, e1)],
    [(24, e1)],
    [(17, e1), (20, e1), (25, e1)]])
private theorem weyl_17_left_s2 : wordMatrix [Atom.rho] = atomMatrix (Atom.rho) := by simp
private def weyl_17_left_m1 : Mat := Sparse.eval (![[(0, e1)],
    [(4, e1)],
    [(3, e1)],
    [(2, e1)],
    [(1, e1)],
    [(11, e1)],
    [(6, e1)],
    [(9, e1)],
    [(17, e1)],
    [(7, e1)],
    [(15, e1)],
    [(0, e1), (5, e1)],
    [(4, e1), (12, e1)],
    [(4, e1), (13, e1)],
    [(20, e1)],
    [(3, e1), (10, e1)],
    [(18, e1)],
    [(0, e1), (2, e1), (8, e1)],
    [(4, e1), (16, e1)],
    [(11, e1), (19, e1)],
    [(3, e1), (6, e1), (14, e1)],
    [(24, e1)],
    [(17, e1), (23, e1)],
    [(11, e1), (15, e1), (22, e1)],
    [(4, e1), (9, e1), (12, e1), (13, e1), (21, e1)],
    [(17, e1), (20, e1), (25, e1)]])
private theorem weyl_17_left_s1 : wordMatrix [Atom.root 10 1, Atom.rho] = weyl_17_left_m1 := by
  rw [wordMatrix_cons, weyl_17_left_s2]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 10 1))
  decide +kernel
private theorem weyl_17_left_s0 : wordMatrix [Atom.rho, Atom.root 10 1, Atom.rho] = weyl_17_target := by
  rw [wordMatrix_cons, weyl_17_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.rho))
  decide +kernel
private theorem weyl_17_left : wordMatrix [Atom.rho, Atom.root 10 1, Atom.rho] = weyl_17_target := weyl_17_left_s0
private theorem weyl_17_right_s0 : wordMatrix [Atom.root 7 1] = atomMatrix (Atom.root 7 1) := by simp
private theorem weyl_17_right : wordMatrix [Atom.root 7 1] = weyl_17_target := by
  rw [weyl_17_right_s0]
  decide +kernel
theorem weyl_17 : wordGroup (weyl_lhs 17) = wordGroup (weyl_rhs 17) := by
  apply word_eq_of_matrix_eq
  exact weyl_17_left.trans weyl_17_right.symm

end Kourovka.Problem2153.WilsonModel.RootData.Relations
