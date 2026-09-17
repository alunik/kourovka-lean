import Kourovka.Problem2153.RankOne.Words
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
namespace Kourovka.Problem2153.RootSystem.NormalGeneration
open RankOne
open WilsonModel Field8 F8
private def Perfect_target : WilsonModel.Mat := Sparse.eval (![[(0, e1)],
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
    [(11, e1)],
    [(12, e1)],
    [(0, e1), (13, e1)],
    [(1, e1), (14, e1)],
    [(15, e1)],
    [(2, e1), (16, e1)],
    [(17, e1)],
    [(3, e1), (18, e1)],
    [(0, e1), (19, e1)],
    [(4, e1), (20, e1)],
    [(1, e1), (5, e1), (21, e1)],
    [(2, e1), (7, e1), (22, e1)],
    [(3, e1), (9, e1), (23, e1)],
    [(4, e1), (11, e1), (24, e1)],
    [(0, e1), (6, e1), (12, e1), (25, e1)]])
private theorem Perfect_left_s3 : wordMatrix [Atom.torus 1 0] = atomMatrix (Atom.torus 1 0) := by simp
private def Perfect_left_m2 : WilsonModel.Mat := Sparse.eval (![[(0, e2)],
    [(1, e1)],
    [(2, e3)],
    [(3, e2)],
    [(4, e6)],
    [(5, e6)],
    [(6, e3)],
    [(7, e1)],
    [(8, e5)],
    [(9, e7)],
    [(10, e6)],
    [(11, e2)],
    [(12, e1)],
    [(0, e7), (13, e1)],
    [(1, e6), (14, e5)],
    [(15, e3)],
    [(2, e1), (16, e4)],
    [(17, e2)],
    [(3, e7), (18, e1)],
    [(0, e3), (19, e6)],
    [(4, e2), (20, e3)],
    [(1, e4), (5, e2), (21, e3)],
    [(2, e7), (7, e6), (22, e5)],
    [(3, e3), (9, e4), (23, e6)],
    [(4, e5), (11, e7), (24, e1)],
    [(0, e4), (6, e7), (12, e6), (25, e5)]])
private theorem Perfect_left_s2 : wordMatrix [Atom.root 11 6, Atom.torus 1 0] = Perfect_left_m2 := by
  rw [wordMatrix_cons, Perfect_left_s3]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 11 6))
  decide +kernel
private def Perfect_left_m1 : WilsonModel.Mat := Sparse.eval (![[(0, e1)],
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
    [(11, e1)],
    [(12, e1)],
    [(0, e7), (13, e1)],
    [(1, e7), (14, e1)],
    [(15, e1)],
    [(2, e7), (16, e1)],
    [(17, e1)],
    [(3, e7), (18, e1)],
    [(0, e5), (19, e1)],
    [(4, e7), (20, e1)],
    [(1, e5), (5, e7), (21, e1)],
    [(2, e5), (7, e7), (22, e1)],
    [(3, e5), (9, e7), (23, e1)],
    [(4, e5), (11, e7), (24, e1)],
    [(0, e3), (6, e5), (12, e7), (25, e1)]])
private theorem Perfect_left_s1 : wordMatrix [Atom.torus 4 0, Atom.root 11 6, Atom.torus 1 0] = Perfect_left_m1 := by
  rw [wordMatrix_cons, Perfect_left_s2]
  apply Sparse.mul_eq_of_check (atomRows (Atom.torus 4 0))
  decide +kernel
private theorem Perfect_left_s0 : wordMatrix [Atom.root 11 6, Atom.torus 4 0, Atom.root 11 6, Atom.torus 1 0] = Perfect_target := by
  rw [wordMatrix_cons, Perfect_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 11 6))
  decide +kernel
private theorem Perfect_left : wordMatrix [Atom.root 11 6, Atom.torus 4 0, Atom.root 11 6, Atom.torus 1 0] = Perfect_target := Perfect_left_s0
private theorem Perfect_right_s0 : wordMatrix [Atom.root 11 1] = atomMatrix (Atom.root 11 1) := by simp
private theorem Perfect_right : wordMatrix [Atom.root 11 1] = Perfect_target := by
  rw [Perfect_right_s0]
  decide +kernel
theorem Perfect_checked : wordGroup [Atom.root 11 6, Atom.torus 4 0, Atom.root 11 6, Atom.torus 1 0] = wordGroup [Atom.root 11 1] := by
  apply word_eq_of_matrix_eq
  exact Perfect_left.trans Perfect_right.symm

end Kourovka.Problem2153.RootSystem.NormalGeneration
