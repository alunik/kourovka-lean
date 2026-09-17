import Kourovka.Problem2153.WilsonModel.RootData.Relations.Metadata
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
namespace Kourovka.Problem2153.WilsonModel.RootData.Relations
open Field8 F8
private def weyl_0_target : Mat := Sparse.eval (![[(0, e1)],
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
private theorem weyl_0_left_s2 : wordMatrix [Atom.rho] = atomMatrix (Atom.rho) := by simp
private def weyl_0_left_m1 : Mat := Sparse.eval (![[(0, e1)],
    [(0, e1), (4, e1)],
    [(3, e1)],
    [(2, e1)],
    [(1, e1)],
    [(2, e1), (11, e1)],
    [(1, e1), (6, e1)],
    [(1, e1), (9, e1)],
    [(1, e1), (6, e1), (9, e1), (17, e1)],
    [(7, e1)],
    [(7, e1), (15, e1)],
    [(5, e1)],
    [(5, e1), (12, e1)],
    [(13, e1)],
    [(5, e1), (13, e1), (20, e1)],
    [(10, e1)],
    [(10, e1), (18, e1)],
    [(8, e1)],
    [(8, e1), (16, e1)],
    [(8, e1), (19, e1)],
    [(14, e1)],
    [(8, e1), (16, e1), (19, e1), (24, e1)],
    [(14, e1), (23, e1)],
    [(22, e1)],
    [(21, e1)],
    [(21, e1), (25, e1)]])
private theorem weyl_0_left_s1 : wordMatrix [Atom.root 0 1, Atom.rho] = weyl_0_left_m1 := by
  rw [wordMatrix_cons, weyl_0_left_s2]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 0 1))
  decide +kernel
private theorem weyl_0_left_s0 : wordMatrix [Atom.rho, Atom.root 0 1, Atom.rho] = weyl_0_target := by
  rw [wordMatrix_cons, weyl_0_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.rho))
  decide +kernel
private theorem weyl_0_left : wordMatrix [Atom.rho, Atom.root 0 1, Atom.rho] = weyl_0_target := weyl_0_left_s0
private theorem weyl_0_right_s0 : wordMatrix [Atom.root 5 1] = atomMatrix (Atom.root 5 1) := by simp
private theorem weyl_0_right : wordMatrix [Atom.root 5 1] = weyl_0_target := by
  rw [weyl_0_right_s0]
  decide +kernel
theorem weyl_0 : wordGroup (weyl_lhs 0) = wordGroup (weyl_rhs 0) := by
  apply word_eq_of_matrix_eq
  exact weyl_0_left.trans weyl_0_right.symm

private def weyl_1_target : Mat := Sparse.eval (![[(0, e1)],
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
    [(9, e1), (13, e1)],
    [(3, e1), (10, e1), (14, e1)],
    [(11, e1), (15, e1)],
    [(4, e1), (9, e1), (12, e1), (13, e1), (16, e1)],
    [(17, e1)],
    [(18, e1)],
    [(11, e1), (15, e1), (19, e1)],
    [(17, e1), (20, e1)],
    [(4, e1), (12, e1), (13, e1), (16, e1), (21, e1)],
    [(11, e1), (19, e1), (22, e1)],
    [(17, e1), (20, e1), (23, e1)],
    [(24, e1)],
    [(17, e1), (23, e1), (25, e1)]])
private theorem weyl_1_left_s2 : wordMatrix [Atom.sigma] = atomMatrix (Atom.sigma) := by simp
private def weyl_1_left_m1 : Mat := Sparse.eval (![[(1, e1)],
    [(0, e1)],
    [(0, e1), (2, e1)],
    [(0, e1), (2, e1), (5, e1)],
    [(0, e1), (5, e1), (8, e1)],
    [(3, e1)],
    [(7, e1)],
    [(3, e1), (6, e1)],
    [(4, e1)],
    [(3, e1), (6, e1), (10, e1)],
    [(4, e1), (9, e1)],
    [(3, e1), (10, e1), (14, e1)],
    [(12, e1), (13, e1)],
    [(9, e1), (13, e1)],
    [(11, e1)],
    [(4, e1), (9, e1), (12, e1), (13, e1), (16, e1)],
    [(11, e1), (15, e1)],
    [(4, e1), (12, e1), (13, e1), (16, e1), (21, e1)],
    [(11, e1), (15, e1), (19, e1)],
    [(18, e1)],
    [(11, e1), (19, e1), (22, e1)],
    [(17, e1)],
    [(17, e1), (20, e1)],
    [(17, e1), (20, e1), (23, e1)],
    [(17, e1), (23, e1), (25, e1)],
    [(24, e1)]])
private theorem weyl_1_left_s1 : wordMatrix [Atom.root 1 1, Atom.sigma] = weyl_1_left_m1 := by
  rw [wordMatrix_cons, weyl_1_left_s2]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 1 1))
  decide +kernel
private theorem weyl_1_left_s0 : wordMatrix [Atom.sigma, Atom.root 1 1, Atom.sigma] = weyl_1_target := by
  rw [wordMatrix_cons, weyl_1_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.sigma))
  decide +kernel
private theorem weyl_1_left : wordMatrix [Atom.sigma, Atom.root 1 1, Atom.sigma] = weyl_1_target := weyl_1_left_s0
private theorem weyl_1_right_s0 : wordMatrix [Atom.root 2 1] = atomMatrix (Atom.root 2 1) := by simp
private theorem weyl_1_right : wordMatrix [Atom.root 2 1] = weyl_1_target := by
  rw [weyl_1_right_s0]
  decide +kernel
theorem weyl_1 : wordGroup (weyl_lhs 1) = wordGroup (weyl_rhs 1) := by
  apply word_eq_of_matrix_eq
  exact weyl_1_left.trans weyl_1_right.symm

private def weyl_2_target : Mat := Sparse.eval (![[(0, e1)],
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
private theorem weyl_2_left_s2 : wordMatrix [Atom.rho] = atomMatrix (Atom.rho) := by simp
private def weyl_2_left_m1 : Mat := Sparse.eval (![[(0, e1)],
    [(4, e1)],
    [(0, e1), (3, e1)],
    [(2, e1)],
    [(1, e1)],
    [(0, e1), (3, e1), (11, e1)],
    [(2, e1), (6, e1)],
    [(9, e1)],
    [(0, e1), (11, e1), (17, e1)],
    [(1, e1), (7, e1)],
    [(2, e1), (6, e1), (15, e1)],
    [(5, e1)],
    [(7, e1), (12, e1)],
    [(7, e1), (13, e1)],
    [(2, e1), (15, e1), (20, e1)],
    [(5, e1), (10, e1)],
    [(1, e1), (7, e1), (12, e1), (13, e1), (18, e1)],
    [(8, e1)],
    [(16, e1)],
    [(5, e1), (10, e1), (19, e1)],
    [(8, e1), (14, e1)],
    [(1, e1), (12, e1), (13, e1), (18, e1), (24, e1)],
    [(5, e1), (19, e1), (23, e1)],
    [(8, e1), (14, e1), (22, e1)],
    [(21, e1)],
    [(8, e1), (22, e1), (25, e1)]])
private theorem weyl_2_left_s1 : wordMatrix [Atom.root 2 1, Atom.rho] = weyl_2_left_m1 := by
  rw [wordMatrix_cons, weyl_2_left_s2]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 2 1))
  decide +kernel
private theorem weyl_2_left_s0 : wordMatrix [Atom.rho, Atom.root 2 1, Atom.rho] = weyl_2_target := by
  rw [wordMatrix_cons, weyl_2_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.rho))
  decide +kernel
private theorem weyl_2_left : wordMatrix [Atom.rho, Atom.root 2 1, Atom.rho] = weyl_2_target := weyl_2_left_s0
private theorem weyl_2_right_s0 : wordMatrix [Atom.root 4 1] = atomMatrix (Atom.root 4 1) := by simp
private theorem weyl_2_right : wordMatrix [Atom.root 4 1] = weyl_2_target := by
  rw [weyl_2_right_s0]
  decide +kernel
theorem weyl_2 : wordGroup (weyl_lhs 2) = wordGroup (weyl_rhs 2) := by
  apply word_eq_of_matrix_eq
  exact weyl_2_left.trans weyl_2_right.symm

private def weyl_3_target : Mat := Sparse.eval (![[(0, e1)],
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
    [(10, e1), (13, e1)],
    [(14, e1)],
    [(8, e1), (10, e1), (12, e1), (15, e1)],
    [(14, e1), (16, e1)],
    [(8, e1), (12, e1), (15, e1), (17, e1)],
    [(14, e1), (16, e1), (18, e1)],
    [(19, e1)],
    [(14, e1), (18, e1), (20, e1)],
    [(21, e1)],
    [(21, e1), (22, e1)],
    [(21, e1), (22, e1), (23, e1)],
    [(21, e1), (23, e1), (24, e1)],
    [(25, e1)]])
private theorem weyl_3_left_s2 : wordMatrix [Atom.sigma] = atomMatrix (Atom.sigma) := by simp
private def weyl_3_left_m1 : Mat := Sparse.eval (![[(1, e1)],
    [(0, e1)],
    [(1, e1), (2, e1)],
    [(5, e1)],
    [(8, e1)],
    [(1, e1), (2, e1), (3, e1)],
    [(5, e1), (7, e1)],
    [(6, e1)],
    [(1, e1), (3, e1), (4, e1)],
    [(8, e1), (10, e1)],
    [(5, e1), (7, e1), (9, e1)],
    [(14, e1)],
    [(10, e1), (12, e1), (13, e1)],
    [(10, e1), (13, e1)],
    [(5, e1), (9, e1), (11, e1)],
    [(14, e1), (16, e1)],
    [(8, e1), (10, e1), (12, e1), (15, e1)],
    [(21, e1)],
    [(19, e1)],
    [(14, e1), (16, e1), (18, e1)],
    [(21, e1), (22, e1)],
    [(8, e1), (12, e1), (15, e1), (17, e1)],
    [(14, e1), (18, e1), (20, e1)],
    [(21, e1), (22, e1), (23, e1)],
    [(25, e1)],
    [(21, e1), (23, e1), (24, e1)]])
private theorem weyl_3_left_s1 : wordMatrix [Atom.root 2 1, Atom.sigma] = weyl_3_left_m1 := by
  rw [wordMatrix_cons, weyl_3_left_s2]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 2 1))
  decide +kernel
private theorem weyl_3_left_s0 : wordMatrix [Atom.sigma, Atom.root 2 1, Atom.sigma] = weyl_3_target := by
  rw [wordMatrix_cons, weyl_3_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.sigma))
  decide +kernel
private theorem weyl_3_left : wordMatrix [Atom.sigma, Atom.root 2 1, Atom.sigma] = weyl_3_target := weyl_3_left_s0
private theorem weyl_3_right_s0 : wordMatrix [Atom.root 1 1] = atomMatrix (Atom.root 1 1) := by simp
private theorem weyl_3_right : wordMatrix [Atom.root 1 1] = weyl_3_target := by
  rw [weyl_3_right_s0]
  decide +kernel
theorem weyl_3 : wordGroup (weyl_lhs 3) = wordGroup (weyl_rhs 3) := by
  apply word_eq_of_matrix_eq
  exact weyl_3_left.trans weyl_3_right.symm

private def weyl_4_target : Mat := Sparse.eval (![[(0, e1)],
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
private theorem weyl_4_left_s2 : wordMatrix [Atom.sigma] = atomMatrix (Atom.sigma) := by simp
private def weyl_4_left_m1 : Mat := Sparse.eval (![[(1, e1)],
    [(0, e1)],
    [(2, e1)],
    [(0, e1), (5, e1)],
    [(0, e1), (2, e1), (8, e1)],
    [(3, e1)],
    [(7, e1)],
    [(6, e1)],
    [(4, e1)],
    [(3, e1), (10, e1)],
    [(9, e1)],
    [(3, e1), (6, e1), (14, e1)],
    [(12, e1), (13, e1)],
    [(4, e1), (13, e1)],
    [(11, e1)],
    [(4, e1), (16, e1)],
    [(15, e1)],
    [(4, e1), (9, e1), (12, e1), (13, e1), (21, e1)],
    [(11, e1), (19, e1)],
    [(18, e1)],
    [(11, e1), (15, e1), (22, e1)],
    [(17, e1)],
    [(20, e1)],
    [(17, e1), (23, e1)],
    [(17, e1), (20, e1), (25, e1)],
    [(24, e1)]])
private theorem weyl_4_left_s1 : wordMatrix [Atom.root 3 1, Atom.sigma] = weyl_4_left_m1 := by
  rw [wordMatrix_cons, weyl_4_left_s2]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 3 1))
  decide +kernel
private theorem weyl_4_left_s0 : wordMatrix [Atom.sigma, Atom.root 3 1, Atom.sigma] = weyl_4_target := by
  rw [wordMatrix_cons, weyl_4_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.sigma))
  decide +kernel
private theorem weyl_4_left : wordMatrix [Atom.sigma, Atom.root 3 1, Atom.sigma] = weyl_4_target := weyl_4_left_s0
private theorem weyl_4_right_s0 : wordMatrix [Atom.root 7 1] = atomMatrix (Atom.root 7 1) := by simp
private theorem weyl_4_right : wordMatrix [Atom.root 7 1] = weyl_4_target := by
  rw [weyl_4_right_s0]
  decide +kernel
theorem weyl_4 : wordGroup (weyl_lhs 4) = wordGroup (weyl_rhs 4) := by
  apply word_eq_of_matrix_eq
  exact weyl_4_left.trans weyl_4_right.symm

private def weyl_5_target : Mat := Sparse.eval (![[(0, e1)],
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
    [(9, e1), (13, e1)],
    [(3, e1), (10, e1), (14, e1)],
    [(11, e1), (15, e1)],
    [(4, e1), (9, e1), (12, e1), (13, e1), (16, e1)],
    [(17, e1)],
    [(18, e1)],
    [(11, e1), (15, e1), (19, e1)],
    [(17, e1), (20, e1)],
    [(4, e1), (12, e1), (13, e1), (16, e1), (21, e1)],
    [(11, e1), (19, e1), (22, e1)],
    [(17, e1), (20, e1), (23, e1)],
    [(24, e1)],
    [(17, e1), (23, e1), (25, e1)]])
private theorem weyl_5_left_s2 : wordMatrix [Atom.rho] = atomMatrix (Atom.rho) := by simp
private def weyl_5_left_m1 : Mat := Sparse.eval (![[(0, e1)],
    [(4, e1)],
    [(3, e1)],
    [(0, e1), (2, e1)],
    [(1, e1)],
    [(11, e1)],
    [(3, e1), (6, e1)],
    [(4, e1), (9, e1)],
    [(17, e1)],
    [(7, e1)],
    [(11, e1), (15, e1)],
    [(0, e1), (2, e1), (5, e1)],
    [(9, e1), (12, e1)],
    [(9, e1), (13, e1)],
    [(17, e1), (20, e1)],
    [(3, e1), (6, e1), (10, e1)],
    [(18, e1)],
    [(0, e1), (5, e1), (8, e1)],
    [(4, e1), (9, e1), (12, e1), (13, e1), (16, e1)],
    [(11, e1), (15, e1), (19, e1)],
    [(3, e1), (10, e1), (14, e1)],
    [(24, e1)],
    [(17, e1), (20, e1), (23, e1)],
    [(11, e1), (19, e1), (22, e1)],
    [(4, e1), (12, e1), (13, e1), (16, e1), (21, e1)],
    [(17, e1), (23, e1), (25, e1)]])
private theorem weyl_5_left_s1 : wordMatrix [Atom.root 4 1, Atom.rho] = weyl_5_left_m1 := by
  rw [wordMatrix_cons, weyl_5_left_s2]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 4 1))
  decide +kernel
private theorem weyl_5_left_s0 : wordMatrix [Atom.rho, Atom.root 4 1, Atom.rho] = weyl_5_target := by
  rw [wordMatrix_cons, weyl_5_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.rho))
  decide +kernel
private theorem weyl_5_left : wordMatrix [Atom.rho, Atom.root 4 1, Atom.rho] = weyl_5_target := weyl_5_left_s0
private theorem weyl_5_right_s0 : wordMatrix [Atom.root 2 1] = atomMatrix (Atom.root 2 1) := by simp
private theorem weyl_5_right : wordMatrix [Atom.root 2 1] = weyl_5_target := by
  rw [weyl_5_right_s0]
  decide +kernel
theorem weyl_5 : wordGroup (weyl_lhs 5) = wordGroup (weyl_rhs 5) := by
  apply word_eq_of_matrix_eq
  exact weyl_5_left.trans weyl_5_right.symm

end Kourovka.Problem2153.WilsonModel.RootData.Relations
