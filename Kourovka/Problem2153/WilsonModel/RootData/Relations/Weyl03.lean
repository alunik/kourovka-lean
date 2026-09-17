import Kourovka.Problem2153.WilsonModel.RootData.Relations.Metadata
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
namespace Kourovka.Problem2153.WilsonModel.RootData.Relations
open Field8 F8
private def weyl_18_target : Mat := Sparse.eval (![[(0, e1)],
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
private theorem weyl_18_left_s2 : wordMatrix [Atom.sigma] = atomMatrix (Atom.sigma) := by simp
private def weyl_18_left_m1 : Mat := Sparse.eval (![[(1, e1)],
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
    [(1, e1), (14, e1)],
    [(0, e1), (12, e1), (13, e1)],
    [(0, e1), (13, e1)],
    [(11, e1)],
    [(2, e1), (16, e1)],
    [(15, e1)],
    [(1, e1), (5, e1), (21, e1)],
    [(0, e1), (19, e1)],
    [(3, e1), (18, e1)],
    [(2, e1), (7, e1), (22, e1)],
    [(17, e1)],
    [(4, e1), (20, e1)],
    [(3, e1), (9, e1), (23, e1)],
    [(0, e1), (6, e1), (12, e1), (25, e1)],
    [(4, e1), (11, e1), (24, e1)]])
private theorem weyl_18_left_s1 : wordMatrix [Atom.root 10 1, Atom.sigma] = weyl_18_left_m1 := by
  rw [wordMatrix_cons, weyl_18_left_s2]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 10 1))
  decide +kernel
private theorem weyl_18_left_s0 : wordMatrix [Atom.sigma, Atom.root 10 1, Atom.sigma] = weyl_18_target := by
  rw [wordMatrix_cons, weyl_18_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.sigma))
  decide +kernel
private theorem weyl_18_left : wordMatrix [Atom.sigma, Atom.root 10 1, Atom.sigma] = weyl_18_target := weyl_18_left_s0
private theorem weyl_18_right_s0 : wordMatrix [Atom.root 11 1] = atomMatrix (Atom.root 11 1) := by simp
private theorem weyl_18_right : wordMatrix [Atom.root 11 1] = weyl_18_target := by
  rw [weyl_18_right_s0]
  decide +kernel
theorem weyl_18 : wordGroup (weyl_lhs 18) = wordGroup (weyl_rhs 18) := by
  apply word_eq_of_matrix_eq
  exact weyl_18_left.trans weyl_18_right.symm

private def weyl_19_target : Mat := Sparse.eval (![[(0, e1)],
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
private theorem weyl_19_left_s2 : wordMatrix [Atom.rho] = atomMatrix (Atom.rho) := by simp
private def weyl_19_left_m1 : Mat := Sparse.eval (![[(0, e1)],
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
    [(0, e1), (13, e1)],
    [(4, e1), (20, e1)],
    [(10, e1)],
    [(3, e1), (18, e1)],
    [(8, e1)],
    [(2, e1), (16, e1)],
    [(0, e1), (19, e1)],
    [(1, e1), (14, e1)],
    [(4, e1), (11, e1), (24, e1)],
    [(3, e1), (9, e1), (23, e1)],
    [(2, e1), (7, e1), (22, e1)],
    [(1, e1), (5, e1), (21, e1)],
    [(0, e1), (6, e1), (12, e1), (25, e1)]])
private theorem weyl_19_left_s1 : wordMatrix [Atom.root 11 1, Atom.rho] = weyl_19_left_m1 := by
  rw [wordMatrix_cons, weyl_19_left_s2]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 11 1))
  decide +kernel
private theorem weyl_19_left_s0 : wordMatrix [Atom.rho, Atom.root 11 1, Atom.rho] = weyl_19_target := by
  rw [wordMatrix_cons, weyl_19_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.rho))
  decide +kernel
private theorem weyl_19_left : wordMatrix [Atom.rho, Atom.root 11 1, Atom.rho] = weyl_19_target := weyl_19_left_s0
private theorem weyl_19_right_s0 : wordMatrix [Atom.root 11 1] = atomMatrix (Atom.root 11 1) := by simp
private theorem weyl_19_right : wordMatrix [Atom.root 11 1] = weyl_19_target := by
  rw [weyl_19_right_s0]
  decide +kernel
theorem weyl_19 : wordGroup (weyl_lhs 19) = wordGroup (weyl_rhs 19) := by
  apply word_eq_of_matrix_eq
  exact weyl_19_left.trans weyl_19_right.symm

private def weyl_20_target : Mat := Sparse.eval (![[(0, e1)],
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
private theorem weyl_20_left_s2 : wordMatrix [Atom.sigma] = atomMatrix (Atom.sigma) := by simp
private def weyl_20_left_m1 : Mat := Sparse.eval (![[(1, e1)],
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
    [(1, e1), (13, e1)],
    [(0, e1), (11, e1)],
    [(16, e1)],
    [(2, e1), (15, e1)],
    [(21, e1)],
    [(5, e1), (19, e1)],
    [(1, e1), (18, e1)],
    [(8, e1), (22, e1)],
    [(0, e1), (3, e1), (17, e1)],
    [(2, e1), (6, e1), (20, e1)],
    [(5, e1), (10, e1), (23, e1)],
    [(8, e1), (14, e1), (25, e1)],
    [(1, e1), (7, e1), (12, e1), (13, e1), (24, e1)]])
private theorem weyl_20_left_s1 : wordMatrix [Atom.root 11 1, Atom.sigma] = weyl_20_left_m1 := by
  rw [wordMatrix_cons, weyl_20_left_s2]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 11 1))
  decide +kernel
private theorem weyl_20_left_s0 : wordMatrix [Atom.sigma, Atom.root 11 1, Atom.sigma] = weyl_20_target := by
  rw [wordMatrix_cons, weyl_20_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.sigma))
  decide +kernel
private theorem weyl_20_left : wordMatrix [Atom.sigma, Atom.root 11 1, Atom.sigma] = weyl_20_target := weyl_20_left_s0
private theorem weyl_20_right_s0 : wordMatrix [Atom.root 10 1] = atomMatrix (Atom.root 10 1) := by simp
private theorem weyl_20_right : wordMatrix [Atom.root 10 1] = weyl_20_target := by
  rw [weyl_20_right_s0]
  decide +kernel
theorem weyl_20 : wordGroup (weyl_lhs 20) = wordGroup (weyl_rhs 20) := by
  apply word_eq_of_matrix_eq
  exact weyl_20_left.trans weyl_20_right.symm

end Kourovka.Problem2153.WilsonModel.RootData.Relations
