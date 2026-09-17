import Kourovka.Problem2153.RankOne.Words
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
namespace Kourovka.Problem2153.RootSystem.NormalGeneration
open RankOne
open WilsonModel Field8 F8
private def SuzukiR_target : WilsonModel.Mat := Sparse.eval (![[(0, e1)],
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
    [(5, e1)],
    [(12, e1)],
    [(13, e1)],
    [(20, e1)],
    [(10, e1)],
    [(18, e1)],
    [(8, e1)],
    [(16, e1)],
    [(19, e1)],
    [(14, e1)],
    [(24, e1)],
    [(23, e1)],
    [(22, e1)],
    [(21, e1)],
    [(25, e1)]])
private theorem SuzukiR_left_s8 : wordMatrix [Atom.root 3 1] = atomMatrix (Atom.root 3 1) := by simp
private def SuzukiR_left_m7 : WilsonModel.Mat := Sparse.eval (![[(0, e1)],
    [(1, e1), (2, e1), (4, e1)],
    [(1, e1), (3, e1)],
    [(2, e1)],
    [(1, e1)],
    [(5, e1), (7, e1), (11, e1)],
    [(6, e1)],
    [(5, e1), (9, e1)],
    [(8, e1), (10, e1), (12, e1), (17, e1)],
    [(7, e1)],
    [(8, e1), (15, e1)],
    [(5, e1)],
    [(12, e1)],
    [(8, e1), (13, e1)],
    [(14, e1), (16, e1), (20, e1)],
    [(10, e1)],
    [(14, e1), (18, e1)],
    [(8, e1)],
    [(16, e1)],
    [(19, e1)],
    [(14, e1)],
    [(21, e1), (22, e1), (24, e1)],
    [(21, e1), (23, e1)],
    [(22, e1)],
    [(21, e1)],
    [(25, e1)]])
private theorem SuzukiR_left_s7 : wordMatrix [Atom.rho, Atom.root 3 1] = SuzukiR_left_m7 := by
  rw [wordMatrix_cons, SuzukiR_left_s8]
  apply Sparse.mul_eq_of_check (atomRows (Atom.rho))
  decide +kernel
private def SuzukiR_left_m6 : WilsonModel.Mat := Sparse.eval (![[(0, e1)],
    [(1, e1), (2, e1), (4, e1)],
    [(1, e1), (3, e1)],
    [(1, e1), (4, e1)],
    [(1, e1), (2, e1), (3, e1), (4, e1)],
    [(5, e1), (7, e1), (11, e1)],
    [(6, e1)],
    [(5, e1), (9, e1)],
    [(8, e1), (10, e1), (12, e1), (17, e1)],
    [(5, e1), (11, e1)],
    [(8, e1), (15, e1)],
    [(5, e1), (7, e1), (9, e1), (11, e1)],
    [(12, e1)],
    [(10, e1), (12, e1), (13, e1), (17, e1)],
    [(14, e1), (16, e1), (20, e1)],
    [(8, e1), (12, e1), (17, e1)],
    [(14, e1), (18, e1)],
    [(8, e1), (10, e1), (15, e1), (17, e1)],
    [(14, e1), (20, e1)],
    [(19, e1)],
    [(14, e1), (16, e1), (18, e1), (20, e1)],
    [(21, e1), (22, e1), (24, e1)],
    [(21, e1), (23, e1)],
    [(21, e1), (24, e1)],
    [(21, e1), (22, e1), (23, e1), (24, e1)],
    [(25, e1)]])
private theorem SuzukiR_left_s6 : wordMatrix [Atom.root 3 1, Atom.rho, Atom.root 3 1] = SuzukiR_left_m6 := by
  rw [wordMatrix_cons, SuzukiR_left_s7]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 3 1))
  decide +kernel
private def SuzukiR_left_m5 : WilsonModel.Mat := Sparse.eval (![[(0, e1)],
    [(1, e1), (2, e1), (3, e1), (4, e1)],
    [(1, e1), (4, e1)],
    [(1, e1), (3, e1)],
    [(1, e1), (2, e1), (4, e1)],
    [(5, e1), (7, e1), (9, e1), (11, e1)],
    [(6, e1)],
    [(5, e1), (11, e1)],
    [(8, e1), (10, e1), (15, e1), (17, e1)],
    [(5, e1), (9, e1)],
    [(8, e1), (12, e1), (17, e1)],
    [(5, e1), (7, e1), (11, e1)],
    [(12, e1)],
    [(10, e1), (12, e1), (13, e1), (17, e1)],
    [(14, e1), (16, e1), (18, e1), (20, e1)],
    [(8, e1), (15, e1)],
    [(14, e1), (20, e1)],
    [(8, e1), (10, e1), (12, e1), (17, e1)],
    [(14, e1), (18, e1)],
    [(19, e1)],
    [(14, e1), (16, e1), (20, e1)],
    [(21, e1), (22, e1), (23, e1), (24, e1)],
    [(21, e1), (24, e1)],
    [(21, e1), (23, e1)],
    [(21, e1), (22, e1), (24, e1)],
    [(25, e1)]])
private theorem SuzukiR_left_s5 : wordMatrix [Atom.rho, Atom.root 3 1, Atom.rho, Atom.root 3 1] = SuzukiR_left_m5 := by
  rw [wordMatrix_cons, SuzukiR_left_s6]
  apply Sparse.mul_eq_of_check (atomRows (Atom.rho))
  decide +kernel
private def SuzukiR_left_m4 : WilsonModel.Mat := Sparse.eval (![[(0, e1)],
    [(1, e1), (2, e1), (3, e1), (4, e1)],
    [(1, e1), (4, e1)],
    [(2, e1), (4, e1)],
    [(1, e1), (3, e1), (4, e1)],
    [(5, e1), (7, e1), (9, e1), (11, e1)],
    [(6, e1)],
    [(5, e1), (11, e1)],
    [(8, e1), (10, e1), (15, e1), (17, e1)],
    [(7, e1), (11, e1)],
    [(8, e1), (12, e1), (17, e1)],
    [(5, e1), (9, e1), (11, e1)],
    [(12, e1)],
    [(8, e1), (12, e1), (13, e1), (15, e1)],
    [(14, e1), (16, e1), (18, e1), (20, e1)],
    [(10, e1), (17, e1)],
    [(14, e1), (20, e1)],
    [(8, e1), (12, e1), (15, e1), (17, e1)],
    [(16, e1), (20, e1)],
    [(19, e1)],
    [(14, e1), (18, e1), (20, e1)],
    [(21, e1), (22, e1), (23, e1), (24, e1)],
    [(21, e1), (24, e1)],
    [(22, e1), (24, e1)],
    [(21, e1), (23, e1), (24, e1)],
    [(25, e1)]])
private theorem SuzukiR_left_s4 : wordMatrix [Atom.root 3 1, Atom.rho, Atom.root 3 1, Atom.rho, Atom.root 3 1] = SuzukiR_left_m4 := by
  rw [wordMatrix_cons, SuzukiR_left_s5]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 3 1))
  decide +kernel
private def SuzukiR_left_m3 : WilsonModel.Mat := Sparse.eval (![[(0, e1)],
    [(1, e1), (3, e1), (4, e1)],
    [(2, e1), (4, e1)],
    [(1, e1), (4, e1)],
    [(1, e1), (2, e1), (3, e1), (4, e1)],
    [(5, e1), (9, e1), (11, e1)],
    [(6, e1)],
    [(7, e1), (11, e1)],
    [(8, e1), (12, e1), (15, e1), (17, e1)],
    [(5, e1), (11, e1)],
    [(10, e1), (17, e1)],
    [(5, e1), (7, e1), (9, e1), (11, e1)],
    [(12, e1)],
    [(8, e1), (12, e1), (13, e1), (15, e1)],
    [(14, e1), (18, e1), (20, e1)],
    [(8, e1), (12, e1), (17, e1)],
    [(16, e1), (20, e1)],
    [(8, e1), (10, e1), (15, e1), (17, e1)],
    [(14, e1), (20, e1)],
    [(19, e1)],
    [(14, e1), (16, e1), (18, e1), (20, e1)],
    [(21, e1), (23, e1), (24, e1)],
    [(22, e1), (24, e1)],
    [(21, e1), (24, e1)],
    [(21, e1), (22, e1), (23, e1), (24, e1)],
    [(25, e1)]])
private theorem SuzukiR_left_s3 : wordMatrix [Atom.rho, Atom.root 3 1, Atom.rho, Atom.root 3 1, Atom.rho, Atom.root 3 1] = SuzukiR_left_m3 := by
  rw [wordMatrix_cons, SuzukiR_left_s4]
  apply Sparse.mul_eq_of_check (atomRows (Atom.rho))
  decide +kernel
private def SuzukiR_left_m2 : WilsonModel.Mat := Sparse.eval (![[(0, e1)],
    [(1, e1), (3, e1), (4, e1)],
    [(2, e1), (4, e1)],
    [(3, e1)],
    [(4, e1)],
    [(5, e1), (9, e1), (11, e1)],
    [(6, e1)],
    [(7, e1), (11, e1)],
    [(8, e1), (12, e1), (15, e1), (17, e1)],
    [(9, e1)],
    [(10, e1), (17, e1)],
    [(11, e1)],
    [(12, e1)],
    [(13, e1), (17, e1)],
    [(14, e1), (18, e1), (20, e1)],
    [(15, e1)],
    [(16, e1), (20, e1)],
    [(17, e1)],
    [(18, e1)],
    [(19, e1)],
    [(20, e1)],
    [(21, e1), (23, e1), (24, e1)],
    [(22, e1), (24, e1)],
    [(23, e1)],
    [(24, e1)],
    [(25, e1)]])
private theorem SuzukiR_left_s2 : wordMatrix [Atom.root 3 1, Atom.rho, Atom.root 3 1, Atom.rho, Atom.root 3 1, Atom.rho, Atom.root 3 1] = SuzukiR_left_m2 := by
  rw [wordMatrix_cons, SuzukiR_left_s3]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 3 1))
  decide +kernel
private def SuzukiR_left_m1 : WilsonModel.Mat := Sparse.eval (![[(0, e1)],
    [(4, e1)],
    [(3, e1)],
    [(2, e1), (4, e1)],
    [(1, e1), (3, e1), (4, e1)],
    [(11, e1)],
    [(6, e1)],
    [(9, e1)],
    [(17, e1)],
    [(7, e1), (11, e1)],
    [(15, e1)],
    [(5, e1), (9, e1), (11, e1)],
    [(12, e1)],
    [(13, e1), (17, e1)],
    [(20, e1)],
    [(10, e1), (17, e1)],
    [(18, e1)],
    [(8, e1), (12, e1), (15, e1), (17, e1)],
    [(16, e1), (20, e1)],
    [(19, e1)],
    [(14, e1), (18, e1), (20, e1)],
    [(24, e1)],
    [(23, e1)],
    [(22, e1), (24, e1)],
    [(21, e1), (23, e1), (24, e1)],
    [(25, e1)]])
private theorem SuzukiR_left_s1 : wordMatrix [Atom.rho, Atom.root 3 1, Atom.rho, Atom.root 3 1, Atom.rho, Atom.root 3 1, Atom.rho, Atom.root 3 1] = SuzukiR_left_m1 := by
  rw [wordMatrix_cons, SuzukiR_left_s2]
  apply Sparse.mul_eq_of_check (atomRows (Atom.rho))
  decide +kernel
private theorem SuzukiR_left_s0 : wordMatrix [Atom.root 3 1, Atom.rho, Atom.root 3 1, Atom.rho, Atom.root 3 1, Atom.rho, Atom.root 3 1, Atom.rho, Atom.root 3 1] = SuzukiR_target := by
  rw [wordMatrix_cons, SuzukiR_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 3 1))
  decide +kernel
private theorem SuzukiR_left : wordMatrix [Atom.root 3 1, Atom.rho, Atom.root 3 1, Atom.rho, Atom.root 3 1, Atom.rho, Atom.root 3 1, Atom.rho, Atom.root 3 1] = SuzukiR_target := SuzukiR_left_s0
private theorem SuzukiR_right_s0 : wordMatrix [Atom.rho] = atomMatrix (Atom.rho) := by simp
private theorem SuzukiR_right : wordMatrix [Atom.rho] = SuzukiR_target := by
  rw [SuzukiR_right_s0]
  decide +kernel
theorem SuzukiR_checked : wordGroup [Atom.root 3 1, Atom.rho, Atom.root 3 1, Atom.rho, Atom.root 3 1, Atom.rho, Atom.root 3 1, Atom.rho, Atom.root 3 1] = wordGroup [Atom.rho] := by
  apply word_eq_of_matrix_eq
  exact SuzukiR_left.trans SuzukiR_right.symm

end Kourovka.Problem2153.RootSystem.NormalGeneration
