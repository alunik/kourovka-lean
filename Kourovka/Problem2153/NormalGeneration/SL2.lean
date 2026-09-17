import Kourovka.Problem2153.RankOne.Words
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
namespace Kourovka.Problem2153.RootSystem.NormalGeneration
open RankOne
open WilsonModel Field8 F8
private def SL2_target : WilsonModel.Mat := Sparse.eval (![[(1, e1)],
    [(0, e1)],
    [(2, e1)],
    [(5, e1)],
    [(8, e1)],
    [(3, e1)],
    [(7, e1)],
    [(6, e1)],
    [(4, e1)],
    [(10, e1)],
    [(9, e1)],
    [(14, e1)],
    [(12, e1), (13, e1)],
    [(13, e1)],
    [(11, e1)],
    [(16, e1)],
    [(15, e1)],
    [(21, e1)],
    [(19, e1)],
    [(18, e1)],
    [(22, e1)],
    [(17, e1)],
    [(20, e1)],
    [(23, e1)],
    [(25, e1)],
    [(24, e1)]])
private theorem SL2_left_s4 : wordMatrix [Atom.root 0 1] = atomMatrix (Atom.root 0 1) := by simp
private def SL2_left_m3 : WilsonModel.Mat := Sparse.eval (![[(0, e1), (1, e1)],
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
private theorem SL2_left_s3 : wordMatrix [Atom.sigma, Atom.root 0 1] = SL2_left_m3 := by
  rw [wordMatrix_cons, SL2_left_s4]
  apply Sparse.mul_eq_of_check (atomRows (Atom.sigma))
  decide +kernel
private def SL2_left_m2 : WilsonModel.Mat := Sparse.eval (![[(0, e1), (1, e1)],
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
private theorem SL2_left_s2 : wordMatrix [Atom.root 0 1, Atom.sigma, Atom.root 0 1] = SL2_left_m2 := by
  rw [wordMatrix_cons, SL2_left_s3]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 0 1))
  decide +kernel
private def SL2_left_m1 : WilsonModel.Mat := Sparse.eval (![[(1, e1)],
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
private theorem SL2_left_s1 : wordMatrix [Atom.sigma, Atom.root 0 1, Atom.sigma, Atom.root 0 1] = SL2_left_m1 := by
  rw [wordMatrix_cons, SL2_left_s2]
  apply Sparse.mul_eq_of_check (atomRows (Atom.sigma))
  decide +kernel
private theorem SL2_left_s0 : wordMatrix [Atom.root 0 1, Atom.sigma, Atom.root 0 1, Atom.sigma, Atom.root 0 1] = SL2_target := by
  rw [wordMatrix_cons, SL2_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 0 1))
  decide +kernel
private theorem SL2_left : wordMatrix [Atom.root 0 1, Atom.sigma, Atom.root 0 1, Atom.sigma, Atom.root 0 1] = SL2_target := SL2_left_s0
private theorem SL2_right_s0 : wordMatrix [Atom.sigma] = atomMatrix (Atom.sigma) := by simp
private theorem SL2_right : wordMatrix [Atom.sigma] = SL2_target := by
  rw [SL2_right_s0]
  decide +kernel
theorem SL2_checked : wordGroup [Atom.root 0 1, Atom.sigma, Atom.root 0 1, Atom.sigma, Atom.root 0 1] = wordGroup [Atom.sigma] := by
  apply word_eq_of_matrix_eq
  exact SL2_left.trans SL2_right.symm

end Kourovka.Problem2153.RootSystem.NormalGeneration
