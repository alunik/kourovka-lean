import Kourovka.Problem2153.RankOne.Cells.Metadata
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
namespace Kourovka.Problem2153.RootSystem.RankOne
open WilsonModel Field8 F8
private def s_cell_0_target : WilsonModel.Mat := Sparse.eval (![[(0, e1), (1, e1)],
    [(1, e1)],
    [(2, e1)],
    [(3, e1), (5, e1)],
    [(4, e1), (6, e1), (7, e1), (8, e1)],
    [(5, e1)],
    [(6, e1), (8, e1)],
    [(7, e1), (8, e1)],
    [(8, e1)],
    [(9, e1), (10, e1)],
    [(10, e1)],
    [(11, e1), (13, e1), (14, e1)],
    [(12, e1), (14, e1)],
    [(13, e1)],
    [(14, e1)],
    [(15, e1), (16, e1)],
    [(16, e1)],
    [(17, e1), (18, e1), (19, e1), (21, e1)],
    [(18, e1), (21, e1)],
    [(19, e1), (21, e1)],
    [(20, e1), (22, e1)],
    [(21, e1)],
    [(22, e1)],
    [(23, e1)],
    [(24, e1), (25, e1)],
    [(25, e1)]])
private theorem s_cell_0_left_s2 : wordMatrix [Atom.sigma] = atomMatrix (Atom.sigma) := by simp
private def s_cell_0_left_m1 : WilsonModel.Mat := Sparse.eval (![[(1, e1)],
    [(0, e1), (1, e1)],
    [(2, e1)],
    [(5, e1)],
    [(8, e1)],
    [(3, e1), (5, e1)],
    [(7, e1), (8, e1)],
    [(6, e1), (8, e1)],
    [(4, e1), (6, e1), (7, e1), (8, e1)],
    [(10, e1)],
    [(9, e1), (10, e1)],
    [(14, e1)],
    [(12, e1), (13, e1), (14, e1)],
    [(13, e1)],
    [(11, e1), (13, e1), (14, e1)],
    [(16, e1)],
    [(15, e1), (16, e1)],
    [(21, e1)],
    [(19, e1), (21, e1)],
    [(18, e1), (21, e1)],
    [(22, e1)],
    [(17, e1), (18, e1), (19, e1), (21, e1)],
    [(20, e1), (22, e1)],
    [(23, e1)],
    [(25, e1)],
    [(24, e1), (25, e1)]])
private theorem s_cell_0_left_s1 : wordMatrix [Atom.root 0 1, Atom.sigma] = s_cell_0_left_m1 := by
  rw [wordMatrix_cons, s_cell_0_left_s2]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 0 1))
  decide +kernel
private theorem s_cell_0_left_s0 : wordMatrix [Atom.sigma, Atom.root 0 1, Atom.sigma] = s_cell_0_target := by
  rw [wordMatrix_cons, s_cell_0_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.sigma))
  decide +kernel
private theorem s_cell_0_left : wordMatrix [Atom.sigma, Atom.root 0 1, Atom.sigma] = s_cell_0_target := s_cell_0_left_s0
private theorem s_cell_0_right_s3 : wordMatrix [Atom.root 0 1] = atomMatrix (Atom.root 0 1) := by simp
private def s_cell_0_right_m2 : WilsonModel.Mat := Sparse.eval (![[(0, e1), (1, e1)],
    [(0, e1)],
    [(2, e1)],
    [(3, e1), (5, e1)],
    [(4, e1), (6, e1), (7, e1), (8, e1)],
    [(3, e1)],
    [(4, e1), (7, e1)],
    [(4, e1), (6, e1)],
    [(4, e1)],
    [(9, e1), (10, e1)],
    [(9, e1)],
    [(11, e1), (13, e1), (14, e1)],
    [(11, e1), (12, e1), (13, e1)],
    [(13, e1)],
    [(11, e1)],
    [(15, e1), (16, e1)],
    [(15, e1)],
    [(17, e1), (18, e1), (19, e1), (21, e1)],
    [(17, e1), (19, e1)],
    [(17, e1), (18, e1)],
    [(20, e1), (22, e1)],
    [(17, e1)],
    [(20, e1)],
    [(23, e1)],
    [(24, e1), (25, e1)],
    [(24, e1)]])
private theorem s_cell_0_right_s2 : wordMatrix [Atom.sigma, Atom.root 0 1] = s_cell_0_right_m2 := by
  rw [wordMatrix_cons, s_cell_0_right_s3]
  apply Sparse.mul_eq_of_check (atomRows (Atom.sigma))
  decide +kernel
private def s_cell_0_right_m1 : WilsonModel.Mat := Sparse.eval (![[(0, e1), (1, e1)],
    [(0, e1)],
    [(2, e1)],
    [(3, e1), (5, e1)],
    [(4, e1), (6, e1), (7, e1), (8, e1)],
    [(3, e1)],
    [(4, e1), (7, e1)],
    [(4, e1), (6, e1)],
    [(4, e1)],
    [(9, e1), (10, e1)],
    [(9, e1)],
    [(11, e1), (13, e1), (14, e1)],
    [(11, e1), (12, e1), (13, e1)],
    [(13, e1)],
    [(11, e1)],
    [(15, e1), (16, e1)],
    [(15, e1)],
    [(17, e1), (18, e1), (19, e1), (21, e1)],
    [(17, e1), (19, e1)],
    [(17, e1), (18, e1)],
    [(20, e1), (22, e1)],
    [(17, e1)],
    [(20, e1)],
    [(23, e1)],
    [(24, e1), (25, e1)],
    [(24, e1)]])
private theorem s_cell_0_right_s1 : wordMatrix [Atom.torus 0 0, Atom.sigma, Atom.root 0 1] = s_cell_0_right_m1 := by
  rw [wordMatrix_cons, s_cell_0_right_s2]
  apply Sparse.mul_eq_of_check (atomRows (Atom.torus 0 0))
  decide +kernel
private theorem s_cell_0_right_s0 : wordMatrix [Atom.root 0 1, Atom.torus 0 0, Atom.sigma, Atom.root 0 1] = s_cell_0_target := by
  rw [wordMatrix_cons, s_cell_0_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 0 1))
  decide +kernel
private theorem s_cell_0_right : wordMatrix [Atom.root 0 1, Atom.torus 0 0, Atom.sigma, Atom.root 0 1] = s_cell_0_target := s_cell_0_right_s0
theorem s_cell_0 : wordGroup (s_lhs 0) = wordGroup (s_rhs 0) := by
  apply word_eq_of_matrix_eq
  exact s_cell_0_left.trans s_cell_0_right.symm

private def s_cell_1_target : WilsonModel.Mat := Sparse.eval (![[(0, e1), (1, e2)],
    [(1, e1)],
    [(2, e1)],
    [(3, e1), (5, e6)],
    [(4, e1), (6, e2), (7, e6), (8, e7)],
    [(5, e1)],
    [(6, e1), (8, e6)],
    [(7, e1), (8, e2)],
    [(8, e1)],
    [(9, e1), (10, e2)],
    [(10, e1)],
    [(11, e1), (13, e2), (14, e4)],
    [(12, e1), (14, e2)],
    [(13, e1)],
    [(14, e1)],
    [(15, e1), (16, e2)],
    [(16, e1)],
    [(17, e1), (18, e2), (19, e6), (21, e7)],
    [(18, e1), (21, e6)],
    [(19, e1), (21, e2)],
    [(20, e1), (22, e6)],
    [(21, e1)],
    [(22, e1)],
    [(23, e1)],
    [(24, e1), (25, e2)],
    [(25, e1)]])
private theorem s_cell_1_left_s2 : wordMatrix [Atom.sigma] = atomMatrix (Atom.sigma) := by simp
private def s_cell_1_left_m1 : WilsonModel.Mat := Sparse.eval (![[(1, e1)],
    [(0, e1), (1, e2)],
    [(2, e1)],
    [(5, e1)],
    [(8, e1)],
    [(3, e1), (5, e6)],
    [(7, e1), (8, e2)],
    [(6, e1), (8, e6)],
    [(4, e1), (6, e2), (7, e6), (8, e7)],
    [(10, e1)],
    [(9, e1), (10, e2)],
    [(14, e1)],
    [(12, e1), (13, e1), (14, e2)],
    [(13, e1)],
    [(11, e1), (13, e2), (14, e4)],
    [(16, e1)],
    [(15, e1), (16, e2)],
    [(21, e1)],
    [(19, e1), (21, e2)],
    [(18, e1), (21, e6)],
    [(22, e1)],
    [(17, e1), (18, e2), (19, e6), (21, e7)],
    [(20, e1), (22, e6)],
    [(23, e1)],
    [(25, e1)],
    [(24, e1), (25, e2)]])
private theorem s_cell_1_left_s1 : wordMatrix [Atom.root 0 2, Atom.sigma] = s_cell_1_left_m1 := by
  rw [wordMatrix_cons, s_cell_1_left_s2]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 0 2))
  decide +kernel
private theorem s_cell_1_left_s0 : wordMatrix [Atom.sigma, Atom.root 0 2, Atom.sigma] = s_cell_1_target := by
  rw [wordMatrix_cons, s_cell_1_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.sigma))
  decide +kernel
private theorem s_cell_1_left : wordMatrix [Atom.sigma, Atom.root 0 2, Atom.sigma] = s_cell_1_target := s_cell_1_left_s0
private theorem s_cell_1_right_s3 : wordMatrix [Atom.root 0 5] = atomMatrix (Atom.root 0 5) := by simp
private def s_cell_1_right_m2 : WilsonModel.Mat := Sparse.eval (![[(0, e5), (1, e1)],
    [(0, e1)],
    [(2, e1)],
    [(3, e3), (5, e1)],
    [(4, e4), (6, e3), (7, e5), (8, e1)],
    [(3, e1)],
    [(4, e3), (7, e1)],
    [(4, e5), (6, e1)],
    [(4, e1)],
    [(9, e5), (10, e1)],
    [(9, e1)],
    [(11, e7), (13, e5), (14, e1)],
    [(11, e5), (12, e1), (13, e1)],
    [(13, e1)],
    [(11, e1)],
    [(15, e5), (16, e1)],
    [(15, e1)],
    [(17, e4), (18, e3), (19, e5), (21, e1)],
    [(17, e3), (19, e1)],
    [(17, e5), (18, e1)],
    [(20, e3), (22, e1)],
    [(17, e1)],
    [(20, e1)],
    [(23, e1)],
    [(24, e5), (25, e1)],
    [(24, e1)]])
private theorem s_cell_1_right_s2 : wordMatrix [Atom.sigma, Atom.root 0 5] = s_cell_1_right_m2 := by
  rw [wordMatrix_cons, s_cell_1_right_s3]
  apply Sparse.mul_eq_of_check (atomRows (Atom.sigma))
  decide +kernel
private def s_cell_1_right_m1 : WilsonModel.Mat := Sparse.eval (![[(0, e1), (1, e2)],
    [(0, e5)],
    [(2, e1)],
    [(3, e1), (5, e6)],
    [(4, e1), (6, e2), (7, e6), (8, e7)],
    [(3, e3)],
    [(4, e5), (7, e3)],
    [(4, e3), (6, e6)],
    [(4, e4)],
    [(9, e1), (10, e2)],
    [(9, e5)],
    [(11, e1), (13, e2), (14, e4)],
    [(11, e5), (12, e1), (13, e1)],
    [(13, e1)],
    [(11, e7)],
    [(15, e1), (16, e2)],
    [(15, e5)],
    [(17, e1), (18, e2), (19, e6), (21, e7)],
    [(17, e5), (19, e3)],
    [(17, e3), (18, e6)],
    [(20, e1), (22, e6)],
    [(17, e4)],
    [(20, e3)],
    [(23, e1)],
    [(24, e1), (25, e2)],
    [(24, e5)]])
private theorem s_cell_1_right_s1 : wordMatrix [Atom.torus 1 4, Atom.sigma, Atom.root 0 5] = s_cell_1_right_m1 := by
  rw [wordMatrix_cons, s_cell_1_right_s2]
  apply Sparse.mul_eq_of_check (atomRows (Atom.torus 1 4))
  decide +kernel
private theorem s_cell_1_right_s0 : wordMatrix [Atom.root 0 5, Atom.torus 1 4, Atom.sigma, Atom.root 0 5] = s_cell_1_target := by
  rw [wordMatrix_cons, s_cell_1_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 0 5))
  decide +kernel
private theorem s_cell_1_right : wordMatrix [Atom.root 0 5, Atom.torus 1 4, Atom.sigma, Atom.root 0 5] = s_cell_1_target := s_cell_1_right_s0
theorem s_cell_1 : wordGroup (s_lhs 1) = wordGroup (s_rhs 1) := by
  apply word_eq_of_matrix_eq
  exact s_cell_1_left.trans s_cell_1_right.symm

private def s_cell_2_target : WilsonModel.Mat := Sparse.eval (![[(0, e1), (1, e3)],
    [(1, e1)],
    [(2, e1)],
    [(3, e1), (5, e7)],
    [(4, e1), (6, e3), (7, e7), (8, e2)],
    [(5, e1)],
    [(6, e1), (8, e7)],
    [(7, e1), (8, e3)],
    [(8, e1)],
    [(9, e1), (10, e3)],
    [(10, e1)],
    [(11, e1), (13, e3), (14, e5)],
    [(12, e1), (14, e3)],
    [(13, e1)],
    [(14, e1)],
    [(15, e1), (16, e3)],
    [(16, e1)],
    [(17, e1), (18, e3), (19, e7), (21, e2)],
    [(18, e1), (21, e7)],
    [(19, e1), (21, e3)],
    [(20, e1), (22, e7)],
    [(21, e1)],
    [(22, e1)],
    [(23, e1)],
    [(24, e1), (25, e3)],
    [(25, e1)]])
private theorem s_cell_2_left_s2 : wordMatrix [Atom.sigma] = atomMatrix (Atom.sigma) := by simp
private def s_cell_2_left_m1 : WilsonModel.Mat := Sparse.eval (![[(1, e1)],
    [(0, e1), (1, e3)],
    [(2, e1)],
    [(5, e1)],
    [(8, e1)],
    [(3, e1), (5, e7)],
    [(7, e1), (8, e3)],
    [(6, e1), (8, e7)],
    [(4, e1), (6, e3), (7, e7), (8, e2)],
    [(10, e1)],
    [(9, e1), (10, e3)],
    [(14, e1)],
    [(12, e1), (13, e1), (14, e3)],
    [(13, e1)],
    [(11, e1), (13, e3), (14, e5)],
    [(16, e1)],
    [(15, e1), (16, e3)],
    [(21, e1)],
    [(19, e1), (21, e3)],
    [(18, e1), (21, e7)],
    [(22, e1)],
    [(17, e1), (18, e3), (19, e7), (21, e2)],
    [(20, e1), (22, e7)],
    [(23, e1)],
    [(25, e1)],
    [(24, e1), (25, e3)]])
private theorem s_cell_2_left_s1 : wordMatrix [Atom.root 0 3, Atom.sigma] = s_cell_2_left_m1 := by
  rw [wordMatrix_cons, s_cell_2_left_s2]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 0 3))
  decide +kernel
private theorem s_cell_2_left_s0 : wordMatrix [Atom.sigma, Atom.root 0 3, Atom.sigma] = s_cell_2_target := by
  rw [wordMatrix_cons, s_cell_2_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.sigma))
  decide +kernel
private theorem s_cell_2_left : wordMatrix [Atom.sigma, Atom.root 0 3, Atom.sigma] = s_cell_2_target := s_cell_2_left_s0
private theorem s_cell_2_right_s3 : wordMatrix [Atom.root 0 6] = atomMatrix (Atom.root 0 6) := by simp
private def s_cell_2_right_m2 : WilsonModel.Mat := Sparse.eval (![[(0, e6), (1, e1)],
    [(0, e1)],
    [(2, e1)],
    [(3, e4), (5, e1)],
    [(4, e5), (6, e4), (7, e6), (8, e1)],
    [(3, e1)],
    [(4, e4), (7, e1)],
    [(4, e6), (6, e1)],
    [(4, e1)],
    [(9, e6), (10, e1)],
    [(9, e1)],
    [(11, e2), (13, e6), (14, e1)],
    [(11, e6), (12, e1), (13, e1)],
    [(13, e1)],
    [(11, e1)],
    [(15, e6), (16, e1)],
    [(15, e1)],
    [(17, e5), (18, e4), (19, e6), (21, e1)],
    [(17, e4), (19, e1)],
    [(17, e6), (18, e1)],
    [(20, e4), (22, e1)],
    [(17, e1)],
    [(20, e1)],
    [(23, e1)],
    [(24, e6), (25, e1)],
    [(24, e1)]])
private theorem s_cell_2_right_s2 : wordMatrix [Atom.sigma, Atom.root 0 6] = s_cell_2_right_m2 := by
  rw [wordMatrix_cons, s_cell_2_right_s3]
  apply Sparse.mul_eq_of_check (atomRows (Atom.sigma))
  decide +kernel
private def s_cell_2_right_m1 : WilsonModel.Mat := Sparse.eval (![[(0, e1), (1, e3)],
    [(0, e6)],
    [(2, e1)],
    [(3, e1), (5, e7)],
    [(4, e1), (6, e3), (7, e7), (8, e2)],
    [(3, e4)],
    [(4, e6), (7, e4)],
    [(4, e4), (6, e7)],
    [(4, e5)],
    [(9, e1), (10, e3)],
    [(9, e6)],
    [(11, e1), (13, e3), (14, e5)],
    [(11, e6), (12, e1), (13, e1)],
    [(13, e1)],
    [(11, e2)],
    [(15, e1), (16, e3)],
    [(15, e6)],
    [(17, e1), (18, e3), (19, e7), (21, e2)],
    [(17, e6), (19, e4)],
    [(17, e4), (18, e7)],
    [(20, e1), (22, e7)],
    [(17, e5)],
    [(20, e4)],
    [(23, e1)],
    [(24, e1), (25, e3)],
    [(24, e6)]])
private theorem s_cell_2_right_s1 : wordMatrix [Atom.torus 2 5, Atom.sigma, Atom.root 0 6] = s_cell_2_right_m1 := by
  rw [wordMatrix_cons, s_cell_2_right_s2]
  apply Sparse.mul_eq_of_check (atomRows (Atom.torus 2 5))
  decide +kernel
private theorem s_cell_2_right_s0 : wordMatrix [Atom.root 0 6, Atom.torus 2 5, Atom.sigma, Atom.root 0 6] = s_cell_2_target := by
  rw [wordMatrix_cons, s_cell_2_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 0 6))
  decide +kernel
private theorem s_cell_2_right : wordMatrix [Atom.root 0 6, Atom.torus 2 5, Atom.sigma, Atom.root 0 6] = s_cell_2_target := s_cell_2_right_s0
theorem s_cell_2 : wordGroup (s_lhs 2) = wordGroup (s_rhs 2) := by
  apply word_eq_of_matrix_eq
  exact s_cell_2_left.trans s_cell_2_right.symm

private def s_cell_3_target : WilsonModel.Mat := Sparse.eval (![[(0, e1), (1, e4)],
    [(1, e1)],
    [(2, e1)],
    [(3, e1), (5, e2)],
    [(4, e1), (6, e4), (7, e2), (8, e3)],
    [(5, e1)],
    [(6, e1), (8, e2)],
    [(7, e1), (8, e4)],
    [(8, e1)],
    [(9, e1), (10, e4)],
    [(10, e1)],
    [(11, e1), (13, e4), (14, e6)],
    [(12, e1), (14, e4)],
    [(13, e1)],
    [(14, e1)],
    [(15, e1), (16, e4)],
    [(16, e1)],
    [(17, e1), (18, e4), (19, e2), (21, e3)],
    [(18, e1), (21, e2)],
    [(19, e1), (21, e4)],
    [(20, e1), (22, e2)],
    [(21, e1)],
    [(22, e1)],
    [(23, e1)],
    [(24, e1), (25, e4)],
    [(25, e1)]])
private theorem s_cell_3_left_s2 : wordMatrix [Atom.sigma] = atomMatrix (Atom.sigma) := by simp
private def s_cell_3_left_m1 : WilsonModel.Mat := Sparse.eval (![[(1, e1)],
    [(0, e1), (1, e4)],
    [(2, e1)],
    [(5, e1)],
    [(8, e1)],
    [(3, e1), (5, e2)],
    [(7, e1), (8, e4)],
    [(6, e1), (8, e2)],
    [(4, e1), (6, e4), (7, e2), (8, e3)],
    [(10, e1)],
    [(9, e1), (10, e4)],
    [(14, e1)],
    [(12, e1), (13, e1), (14, e4)],
    [(13, e1)],
    [(11, e1), (13, e4), (14, e6)],
    [(16, e1)],
    [(15, e1), (16, e4)],
    [(21, e1)],
    [(19, e1), (21, e4)],
    [(18, e1), (21, e2)],
    [(22, e1)],
    [(17, e1), (18, e4), (19, e2), (21, e3)],
    [(20, e1), (22, e2)],
    [(23, e1)],
    [(25, e1)],
    [(24, e1), (25, e4)]])
private theorem s_cell_3_left_s1 : wordMatrix [Atom.root 0 4, Atom.sigma] = s_cell_3_left_m1 := by
  rw [wordMatrix_cons, s_cell_3_left_s2]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 0 4))
  decide +kernel
private theorem s_cell_3_left_s0 : wordMatrix [Atom.sigma, Atom.root 0 4, Atom.sigma] = s_cell_3_target := by
  rw [wordMatrix_cons, s_cell_3_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.sigma))
  decide +kernel
private theorem s_cell_3_left : wordMatrix [Atom.sigma, Atom.root 0 4, Atom.sigma] = s_cell_3_target := s_cell_3_left_s0
private theorem s_cell_3_right_s3 : wordMatrix [Atom.root 0 7] = atomMatrix (Atom.root 0 7) := by simp
private def s_cell_3_right_m2 : WilsonModel.Mat := Sparse.eval (![[(0, e7), (1, e1)],
    [(0, e1)],
    [(2, e1)],
    [(3, e5), (5, e1)],
    [(4, e6), (6, e5), (7, e7), (8, e1)],
    [(3, e1)],
    [(4, e5), (7, e1)],
    [(4, e7), (6, e1)],
    [(4, e1)],
    [(9, e7), (10, e1)],
    [(9, e1)],
    [(11, e3), (13, e7), (14, e1)],
    [(11, e7), (12, e1), (13, e1)],
    [(13, e1)],
    [(11, e1)],
    [(15, e7), (16, e1)],
    [(15, e1)],
    [(17, e6), (18, e5), (19, e7), (21, e1)],
    [(17, e5), (19, e1)],
    [(17, e7), (18, e1)],
    [(20, e5), (22, e1)],
    [(17, e1)],
    [(20, e1)],
    [(23, e1)],
    [(24, e7), (25, e1)],
    [(24, e1)]])
private theorem s_cell_3_right_s2 : wordMatrix [Atom.sigma, Atom.root 0 7] = s_cell_3_right_m2 := by
  rw [wordMatrix_cons, s_cell_3_right_s3]
  apply Sparse.mul_eq_of_check (atomRows (Atom.sigma))
  decide +kernel
private def s_cell_3_right_m1 : WilsonModel.Mat := Sparse.eval (![[(0, e1), (1, e4)],
    [(0, e7)],
    [(2, e1)],
    [(3, e1), (5, e2)],
    [(4, e1), (6, e4), (7, e2), (8, e3)],
    [(3, e5)],
    [(4, e7), (7, e5)],
    [(4, e5), (6, e2)],
    [(4, e6)],
    [(9, e1), (10, e4)],
    [(9, e7)],
    [(11, e1), (13, e4), (14, e6)],
    [(11, e7), (12, e1), (13, e1)],
    [(13, e1)],
    [(11, e3)],
    [(15, e1), (16, e4)],
    [(15, e7)],
    [(17, e1), (18, e4), (19, e2), (21, e3)],
    [(17, e7), (19, e5)],
    [(17, e5), (18, e2)],
    [(20, e1), (22, e2)],
    [(17, e6)],
    [(20, e5)],
    [(23, e1)],
    [(24, e1), (25, e4)],
    [(24, e7)]])
private theorem s_cell_3_right_s1 : wordMatrix [Atom.torus 3 6, Atom.sigma, Atom.root 0 7] = s_cell_3_right_m1 := by
  rw [wordMatrix_cons, s_cell_3_right_s2]
  apply Sparse.mul_eq_of_check (atomRows (Atom.torus 3 6))
  decide +kernel
private theorem s_cell_3_right_s0 : wordMatrix [Atom.root 0 7, Atom.torus 3 6, Atom.sigma, Atom.root 0 7] = s_cell_3_target := by
  rw [wordMatrix_cons, s_cell_3_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 0 7))
  decide +kernel
private theorem s_cell_3_right : wordMatrix [Atom.root 0 7, Atom.torus 3 6, Atom.sigma, Atom.root 0 7] = s_cell_3_target := s_cell_3_right_s0
theorem s_cell_3 : wordGroup (s_lhs 3) = wordGroup (s_rhs 3) := by
  apply word_eq_of_matrix_eq
  exact s_cell_3_left.trans s_cell_3_right.symm

private def s_cell_4_target : WilsonModel.Mat := Sparse.eval (![[(0, e1), (1, e5)],
    [(1, e1)],
    [(2, e1)],
    [(3, e1), (5, e3)],
    [(4, e1), (6, e5), (7, e3), (8, e4)],
    [(5, e1)],
    [(6, e1), (8, e3)],
    [(7, e1), (8, e5)],
    [(8, e1)],
    [(9, e1), (10, e5)],
    [(10, e1)],
    [(11, e1), (13, e5), (14, e7)],
    [(12, e1), (14, e5)],
    [(13, e1)],
    [(14, e1)],
    [(15, e1), (16, e5)],
    [(16, e1)],
    [(17, e1), (18, e5), (19, e3), (21, e4)],
    [(18, e1), (21, e3)],
    [(19, e1), (21, e5)],
    [(20, e1), (22, e3)],
    [(21, e1)],
    [(22, e1)],
    [(23, e1)],
    [(24, e1), (25, e5)],
    [(25, e1)]])
private theorem s_cell_4_left_s2 : wordMatrix [Atom.sigma] = atomMatrix (Atom.sigma) := by simp
private def s_cell_4_left_m1 : WilsonModel.Mat := Sparse.eval (![[(1, e1)],
    [(0, e1), (1, e5)],
    [(2, e1)],
    [(5, e1)],
    [(8, e1)],
    [(3, e1), (5, e3)],
    [(7, e1), (8, e5)],
    [(6, e1), (8, e3)],
    [(4, e1), (6, e5), (7, e3), (8, e4)],
    [(10, e1)],
    [(9, e1), (10, e5)],
    [(14, e1)],
    [(12, e1), (13, e1), (14, e5)],
    [(13, e1)],
    [(11, e1), (13, e5), (14, e7)],
    [(16, e1)],
    [(15, e1), (16, e5)],
    [(21, e1)],
    [(19, e1), (21, e5)],
    [(18, e1), (21, e3)],
    [(22, e1)],
    [(17, e1), (18, e5), (19, e3), (21, e4)],
    [(20, e1), (22, e3)],
    [(23, e1)],
    [(25, e1)],
    [(24, e1), (25, e5)]])
private theorem s_cell_4_left_s1 : wordMatrix [Atom.root 0 5, Atom.sigma] = s_cell_4_left_m1 := by
  rw [wordMatrix_cons, s_cell_4_left_s2]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 0 5))
  decide +kernel
private theorem s_cell_4_left_s0 : wordMatrix [Atom.sigma, Atom.root 0 5, Atom.sigma] = s_cell_4_target := by
  rw [wordMatrix_cons, s_cell_4_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.sigma))
  decide +kernel
private theorem s_cell_4_left : wordMatrix [Atom.sigma, Atom.root 0 5, Atom.sigma] = s_cell_4_target := s_cell_4_left_s0
private theorem s_cell_4_right_s3 : wordMatrix [Atom.root 0 2] = atomMatrix (Atom.root 0 2) := by simp
private def s_cell_4_right_m2 : WilsonModel.Mat := Sparse.eval (![[(0, e2), (1, e1)],
    [(0, e1)],
    [(2, e1)],
    [(3, e6), (5, e1)],
    [(4, e7), (6, e6), (7, e2), (8, e1)],
    [(3, e1)],
    [(4, e6), (7, e1)],
    [(4, e2), (6, e1)],
    [(4, e1)],
    [(9, e2), (10, e1)],
    [(9, e1)],
    [(11, e4), (13, e2), (14, e1)],
    [(11, e2), (12, e1), (13, e1)],
    [(13, e1)],
    [(11, e1)],
    [(15, e2), (16, e1)],
    [(15, e1)],
    [(17, e7), (18, e6), (19, e2), (21, e1)],
    [(17, e6), (19, e1)],
    [(17, e2), (18, e1)],
    [(20, e6), (22, e1)],
    [(17, e1)],
    [(20, e1)],
    [(23, e1)],
    [(24, e2), (25, e1)],
    [(24, e1)]])
private theorem s_cell_4_right_s2 : wordMatrix [Atom.sigma, Atom.root 0 2] = s_cell_4_right_m2 := by
  rw [wordMatrix_cons, s_cell_4_right_s3]
  apply Sparse.mul_eq_of_check (atomRows (Atom.sigma))
  decide +kernel
private def s_cell_4_right_m1 : WilsonModel.Mat := Sparse.eval (![[(0, e1), (1, e5)],
    [(0, e2)],
    [(2, e1)],
    [(3, e1), (5, e3)],
    [(4, e1), (6, e5), (7, e3), (8, e4)],
    [(3, e6)],
    [(4, e2), (7, e6)],
    [(4, e6), (6, e3)],
    [(4, e7)],
    [(9, e1), (10, e5)],
    [(9, e2)],
    [(11, e1), (13, e5), (14, e7)],
    [(11, e2), (12, e1), (13, e1)],
    [(13, e1)],
    [(11, e4)],
    [(15, e1), (16, e5)],
    [(15, e2)],
    [(17, e1), (18, e5), (19, e3), (21, e4)],
    [(17, e2), (19, e6)],
    [(17, e6), (18, e3)],
    [(20, e1), (22, e3)],
    [(17, e7)],
    [(20, e6)],
    [(23, e1)],
    [(24, e1), (25, e5)],
    [(24, e2)]])
private theorem s_cell_4_right_s1 : wordMatrix [Atom.torus 4 1, Atom.sigma, Atom.root 0 2] = s_cell_4_right_m1 := by
  rw [wordMatrix_cons, s_cell_4_right_s2]
  apply Sparse.mul_eq_of_check (atomRows (Atom.torus 4 1))
  decide +kernel
private theorem s_cell_4_right_s0 : wordMatrix [Atom.root 0 2, Atom.torus 4 1, Atom.sigma, Atom.root 0 2] = s_cell_4_target := by
  rw [wordMatrix_cons, s_cell_4_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 0 2))
  decide +kernel
private theorem s_cell_4_right : wordMatrix [Atom.root 0 2, Atom.torus 4 1, Atom.sigma, Atom.root 0 2] = s_cell_4_target := s_cell_4_right_s0
theorem s_cell_4 : wordGroup (s_lhs 4) = wordGroup (s_rhs 4) := by
  apply word_eq_of_matrix_eq
  exact s_cell_4_left.trans s_cell_4_right.symm

private def s_cell_5_target : WilsonModel.Mat := Sparse.eval (![[(0, e1), (1, e6)],
    [(1, e1)],
    [(2, e1)],
    [(3, e1), (5, e4)],
    [(4, e1), (6, e6), (7, e4), (8, e5)],
    [(5, e1)],
    [(6, e1), (8, e4)],
    [(7, e1), (8, e6)],
    [(8, e1)],
    [(9, e1), (10, e6)],
    [(10, e1)],
    [(11, e1), (13, e6), (14, e2)],
    [(12, e1), (14, e6)],
    [(13, e1)],
    [(14, e1)],
    [(15, e1), (16, e6)],
    [(16, e1)],
    [(17, e1), (18, e6), (19, e4), (21, e5)],
    [(18, e1), (21, e4)],
    [(19, e1), (21, e6)],
    [(20, e1), (22, e4)],
    [(21, e1)],
    [(22, e1)],
    [(23, e1)],
    [(24, e1), (25, e6)],
    [(25, e1)]])
private theorem s_cell_5_left_s2 : wordMatrix [Atom.sigma] = atomMatrix (Atom.sigma) := by simp
private def s_cell_5_left_m1 : WilsonModel.Mat := Sparse.eval (![[(1, e1)],
    [(0, e1), (1, e6)],
    [(2, e1)],
    [(5, e1)],
    [(8, e1)],
    [(3, e1), (5, e4)],
    [(7, e1), (8, e6)],
    [(6, e1), (8, e4)],
    [(4, e1), (6, e6), (7, e4), (8, e5)],
    [(10, e1)],
    [(9, e1), (10, e6)],
    [(14, e1)],
    [(12, e1), (13, e1), (14, e6)],
    [(13, e1)],
    [(11, e1), (13, e6), (14, e2)],
    [(16, e1)],
    [(15, e1), (16, e6)],
    [(21, e1)],
    [(19, e1), (21, e6)],
    [(18, e1), (21, e4)],
    [(22, e1)],
    [(17, e1), (18, e6), (19, e4), (21, e5)],
    [(20, e1), (22, e4)],
    [(23, e1)],
    [(25, e1)],
    [(24, e1), (25, e6)]])
private theorem s_cell_5_left_s1 : wordMatrix [Atom.root 0 6, Atom.sigma] = s_cell_5_left_m1 := by
  rw [wordMatrix_cons, s_cell_5_left_s2]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 0 6))
  decide +kernel
private theorem s_cell_5_left_s0 : wordMatrix [Atom.sigma, Atom.root 0 6, Atom.sigma] = s_cell_5_target := by
  rw [wordMatrix_cons, s_cell_5_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.sigma))
  decide +kernel
private theorem s_cell_5_left : wordMatrix [Atom.sigma, Atom.root 0 6, Atom.sigma] = s_cell_5_target := s_cell_5_left_s0
private theorem s_cell_5_right_s3 : wordMatrix [Atom.root 0 3] = atomMatrix (Atom.root 0 3) := by simp
private def s_cell_5_right_m2 : WilsonModel.Mat := Sparse.eval (![[(0, e3), (1, e1)],
    [(0, e1)],
    [(2, e1)],
    [(3, e7), (5, e1)],
    [(4, e2), (6, e7), (7, e3), (8, e1)],
    [(3, e1)],
    [(4, e7), (7, e1)],
    [(4, e3), (6, e1)],
    [(4, e1)],
    [(9, e3), (10, e1)],
    [(9, e1)],
    [(11, e5), (13, e3), (14, e1)],
    [(11, e3), (12, e1), (13, e1)],
    [(13, e1)],
    [(11, e1)],
    [(15, e3), (16, e1)],
    [(15, e1)],
    [(17, e2), (18, e7), (19, e3), (21, e1)],
    [(17, e7), (19, e1)],
    [(17, e3), (18, e1)],
    [(20, e7), (22, e1)],
    [(17, e1)],
    [(20, e1)],
    [(23, e1)],
    [(24, e3), (25, e1)],
    [(24, e1)]])
private theorem s_cell_5_right_s2 : wordMatrix [Atom.sigma, Atom.root 0 3] = s_cell_5_right_m2 := by
  rw [wordMatrix_cons, s_cell_5_right_s3]
  apply Sparse.mul_eq_of_check (atomRows (Atom.sigma))
  decide +kernel
private def s_cell_5_right_m1 : WilsonModel.Mat := Sparse.eval (![[(0, e1), (1, e6)],
    [(0, e3)],
    [(2, e1)],
    [(3, e1), (5, e4)],
    [(4, e1), (6, e6), (7, e4), (8, e5)],
    [(3, e7)],
    [(4, e3), (7, e7)],
    [(4, e7), (6, e4)],
    [(4, e2)],
    [(9, e1), (10, e6)],
    [(9, e3)],
    [(11, e1), (13, e6), (14, e2)],
    [(11, e3), (12, e1), (13, e1)],
    [(13, e1)],
    [(11, e5)],
    [(15, e1), (16, e6)],
    [(15, e3)],
    [(17, e1), (18, e6), (19, e4), (21, e5)],
    [(17, e3), (19, e7)],
    [(17, e7), (18, e4)],
    [(20, e1), (22, e4)],
    [(17, e2)],
    [(20, e7)],
    [(23, e1)],
    [(24, e1), (25, e6)],
    [(24, e3)]])
private theorem s_cell_5_right_s1 : wordMatrix [Atom.torus 5 2, Atom.sigma, Atom.root 0 3] = s_cell_5_right_m1 := by
  rw [wordMatrix_cons, s_cell_5_right_s2]
  apply Sparse.mul_eq_of_check (atomRows (Atom.torus 5 2))
  decide +kernel
private theorem s_cell_5_right_s0 : wordMatrix [Atom.root 0 3, Atom.torus 5 2, Atom.sigma, Atom.root 0 3] = s_cell_5_target := by
  rw [wordMatrix_cons, s_cell_5_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 0 3))
  decide +kernel
private theorem s_cell_5_right : wordMatrix [Atom.root 0 3, Atom.torus 5 2, Atom.sigma, Atom.root 0 3] = s_cell_5_target := s_cell_5_right_s0
theorem s_cell_5 : wordGroup (s_lhs 5) = wordGroup (s_rhs 5) := by
  apply word_eq_of_matrix_eq
  exact s_cell_5_left.trans s_cell_5_right.symm

end Kourovka.Problem2153.RootSystem.RankOne
