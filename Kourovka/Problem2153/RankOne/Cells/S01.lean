import Kourovka.Problem2153.RankOne.Cells.Metadata
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
namespace Kourovka.Problem2153.RootSystem.RankOne
open WilsonModel Field8 F8
private def s_cell_6_target : WilsonModel.Mat := Sparse.eval (![[(0, e1), (1, e7)],
    [(1, e1)],
    [(2, e1)],
    [(3, e1), (5, e5)],
    [(4, e1), (6, e7), (7, e5), (8, e6)],
    [(5, e1)],
    [(6, e1), (8, e5)],
    [(7, e1), (8, e7)],
    [(8, e1)],
    [(9, e1), (10, e7)],
    [(10, e1)],
    [(11, e1), (13, e7), (14, e3)],
    [(12, e1), (14, e7)],
    [(13, e1)],
    [(14, e1)],
    [(15, e1), (16, e7)],
    [(16, e1)],
    [(17, e1), (18, e7), (19, e5), (21, e6)],
    [(18, e1), (21, e5)],
    [(19, e1), (21, e7)],
    [(20, e1), (22, e5)],
    [(21, e1)],
    [(22, e1)],
    [(23, e1)],
    [(24, e1), (25, e7)],
    [(25, e1)]])
private theorem s_cell_6_left_s2 : wordMatrix [Atom.sigma] = atomMatrix (Atom.sigma) := by simp
private def s_cell_6_left_m1 : WilsonModel.Mat := Sparse.eval (![[(1, e1)],
    [(0, e1), (1, e7)],
    [(2, e1)],
    [(5, e1)],
    [(8, e1)],
    [(3, e1), (5, e5)],
    [(7, e1), (8, e7)],
    [(6, e1), (8, e5)],
    [(4, e1), (6, e7), (7, e5), (8, e6)],
    [(10, e1)],
    [(9, e1), (10, e7)],
    [(14, e1)],
    [(12, e1), (13, e1), (14, e7)],
    [(13, e1)],
    [(11, e1), (13, e7), (14, e3)],
    [(16, e1)],
    [(15, e1), (16, e7)],
    [(21, e1)],
    [(19, e1), (21, e7)],
    [(18, e1), (21, e5)],
    [(22, e1)],
    [(17, e1), (18, e7), (19, e5), (21, e6)],
    [(20, e1), (22, e5)],
    [(23, e1)],
    [(25, e1)],
    [(24, e1), (25, e7)]])
private theorem s_cell_6_left_s1 : wordMatrix [Atom.root 0 7, Atom.sigma] = s_cell_6_left_m1 := by
  rw [wordMatrix_cons, s_cell_6_left_s2]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 0 7))
  decide +kernel
private theorem s_cell_6_left_s0 : wordMatrix [Atom.sigma, Atom.root 0 7, Atom.sigma] = s_cell_6_target := by
  rw [wordMatrix_cons, s_cell_6_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.sigma))
  decide +kernel
private theorem s_cell_6_left : wordMatrix [Atom.sigma, Atom.root 0 7, Atom.sigma] = s_cell_6_target := s_cell_6_left_s0
private theorem s_cell_6_right_s3 : wordMatrix [Atom.root 0 4] = atomMatrix (Atom.root 0 4) := by simp
private def s_cell_6_right_m2 : WilsonModel.Mat := Sparse.eval (![[(0, e4), (1, e1)],
    [(0, e1)],
    [(2, e1)],
    [(3, e2), (5, e1)],
    [(4, e3), (6, e2), (7, e4), (8, e1)],
    [(3, e1)],
    [(4, e2), (7, e1)],
    [(4, e4), (6, e1)],
    [(4, e1)],
    [(9, e4), (10, e1)],
    [(9, e1)],
    [(11, e6), (13, e4), (14, e1)],
    [(11, e4), (12, e1), (13, e1)],
    [(13, e1)],
    [(11, e1)],
    [(15, e4), (16, e1)],
    [(15, e1)],
    [(17, e3), (18, e2), (19, e4), (21, e1)],
    [(17, e2), (19, e1)],
    [(17, e4), (18, e1)],
    [(20, e2), (22, e1)],
    [(17, e1)],
    [(20, e1)],
    [(23, e1)],
    [(24, e4), (25, e1)],
    [(24, e1)]])
private theorem s_cell_6_right_s2 : wordMatrix [Atom.sigma, Atom.root 0 4] = s_cell_6_right_m2 := by
  rw [wordMatrix_cons, s_cell_6_right_s3]
  apply Sparse.mul_eq_of_check (atomRows (Atom.sigma))
  decide +kernel
private def s_cell_6_right_m1 : WilsonModel.Mat := Sparse.eval (![[(0, e1), (1, e7)],
    [(0, e4)],
    [(2, e1)],
    [(3, e1), (5, e5)],
    [(4, e1), (6, e7), (7, e5), (8, e6)],
    [(3, e2)],
    [(4, e4), (7, e2)],
    [(4, e2), (6, e5)],
    [(4, e3)],
    [(9, e1), (10, e7)],
    [(9, e4)],
    [(11, e1), (13, e7), (14, e3)],
    [(11, e4), (12, e1), (13, e1)],
    [(13, e1)],
    [(11, e6)],
    [(15, e1), (16, e7)],
    [(15, e4)],
    [(17, e1), (18, e7), (19, e5), (21, e6)],
    [(17, e4), (19, e2)],
    [(17, e2), (18, e5)],
    [(20, e1), (22, e5)],
    [(17, e3)],
    [(20, e2)],
    [(23, e1)],
    [(24, e1), (25, e7)],
    [(24, e4)]])
private theorem s_cell_6_right_s1 : wordMatrix [Atom.torus 6 3, Atom.sigma, Atom.root 0 4] = s_cell_6_right_m1 := by
  rw [wordMatrix_cons, s_cell_6_right_s2]
  apply Sparse.mul_eq_of_check (atomRows (Atom.torus 6 3))
  decide +kernel
private theorem s_cell_6_right_s0 : wordMatrix [Atom.root 0 4, Atom.torus 6 3, Atom.sigma, Atom.root 0 4] = s_cell_6_target := by
  rw [wordMatrix_cons, s_cell_6_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 0 4))
  decide +kernel
private theorem s_cell_6_right : wordMatrix [Atom.root 0 4, Atom.torus 6 3, Atom.sigma, Atom.root 0 4] = s_cell_6_target := s_cell_6_right_s0
theorem s_cell_6 : wordGroup (s_lhs 6) = wordGroup (s_rhs 6) := by
  apply word_eq_of_matrix_eq
  exact s_cell_6_left.trans s_cell_6_right.symm

end Kourovka.Problem2153.RootSystem.RankOne
