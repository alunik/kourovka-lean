import Kourovka.Problem2153.WilsonModel.RootData.Relations.Metadata
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
namespace Kourovka.Problem2153.WilsonModel.RootData.Relations
open Field8 F8
private def inverse_0_target : Mat := 1
private theorem inverse_0_left_s1 : wordMatrix [Atom.root 0 1] = atomMatrix (Atom.root 0 1) := by simp
private theorem inverse_0_left_s0 : wordMatrix [Atom.root 0 1, Atom.root 0 1] = inverse_0_target := by
  rw [wordMatrix_cons, inverse_0_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 0 1))
  decide +kernel
private theorem inverse_0_left : wordMatrix [Atom.root 0 1, Atom.root 0 1] = inverse_0_target := inverse_0_left_s0
private theorem inverse_0_right : wordMatrix [] = inverse_0_target := by decide +kernel
theorem inverse_0 : wordGroup (inverse_lhs 0) = wordGroup (inverse_rhs 0) := by
  apply word_eq_of_matrix_eq
  exact inverse_0_left.trans inverse_0_right.symm

private def inverse_1_target : Mat := 1
private theorem inverse_1_left_s2 : wordMatrix [Atom.root 3 1] = atomMatrix (Atom.root 3 1) := by simp
private def inverse_1_left_m1 : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(1, e1), (2, e1)],
    [(2, e1), (3, e1)],
    [(1, e1), (2, e1), (3, e1), (4, e1)],
    [(5, e1)],
    [(6, e1)],
    [(5, e1), (7, e1)],
    [(8, e1)],
    [(7, e1), (9, e1)],
    [(8, e1), (10, e1)],
    [(5, e1), (7, e1), (9, e1), (11, e1)],
    [(12, e1)],
    [(8, e1), (10, e1), (13, e1)],
    [(14, e1)],
    [(10, e1), (12, e1), (15, e1)],
    [(14, e1), (16, e1)],
    [(8, e1), (10, e1), (15, e1), (17, e1)],
    [(16, e1), (18, e1)],
    [(19, e1)],
    [(14, e1), (16, e1), (18, e1), (20, e1)],
    [(21, e1)],
    [(21, e1), (22, e1)],
    [(22, e1), (23, e1)],
    [(21, e1), (22, e1), (23, e1), (24, e1)],
    [(25, e1)]])
private theorem inverse_1_left_s1 : wordMatrix [Atom.root 1 1, Atom.root 3 1] = inverse_1_left_m1 := by
  rw [wordMatrix_cons, inverse_1_left_s2]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 1 1))
  decide +kernel
private theorem inverse_1_left_s0 : wordMatrix [Atom.root 1 1, Atom.root 1 1, Atom.root 3 1] = inverse_1_target := by
  rw [wordMatrix_cons, inverse_1_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 1 1))
  decide +kernel
private theorem inverse_1_left : wordMatrix [Atom.root 1 1, Atom.root 1 1, Atom.root 3 1] = inverse_1_target := inverse_1_left_s0
private theorem inverse_1_right : wordMatrix [] = inverse_1_target := by decide +kernel
theorem inverse_1 : wordGroup (inverse_lhs 1) = wordGroup (inverse_rhs 1) := by
  apply word_eq_of_matrix_eq
  exact inverse_1_left.trans inverse_1_right.symm

private def inverse_2_target : Mat := 1
private theorem inverse_2_left_s2 : wordMatrix [Atom.root 7 1] = atomMatrix (Atom.root 7 1) := by simp
private def inverse_2_left_m1 : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(0, e1), (2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(2, e1), (5, e1)],
    [(3, e1), (6, e1)],
    [(7, e1)],
    [(0, e1), (2, e1), (5, e1), (8, e1)],
    [(4, e1), (9, e1)],
    [(6, e1), (10, e1)],
    [(11, e1)],
    [(4, e1), (9, e1), (12, e1)],
    [(4, e1), (9, e1), (13, e1)],
    [(3, e1), (6, e1), (10, e1), (14, e1)],
    [(11, e1), (15, e1)],
    [(9, e1), (12, e1), (13, e1), (16, e1)],
    [(17, e1)],
    [(18, e1)],
    [(15, e1), (19, e1)],
    [(17, e1), (20, e1)],
    [(4, e1), (9, e1), (16, e1), (21, e1)],
    [(11, e1), (15, e1), (19, e1), (22, e1)],
    [(20, e1), (23, e1)],
    [(24, e1)],
    [(17, e1), (20, e1), (23, e1), (25, e1)]])
private theorem inverse_2_left_s1 : wordMatrix [Atom.root 2 1, Atom.root 7 1] = inverse_2_left_m1 := by
  rw [wordMatrix_cons, inverse_2_left_s2]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 2 1))
  decide +kernel
private theorem inverse_2_left_s0 : wordMatrix [Atom.root 2 1, Atom.root 2 1, Atom.root 7 1] = inverse_2_target := by
  rw [wordMatrix_cons, inverse_2_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 2 1))
  decide +kernel
private theorem inverse_2_left : wordMatrix [Atom.root 2 1, Atom.root 2 1, Atom.root 7 1] = inverse_2_target := inverse_2_left_s0
private theorem inverse_2_right : wordMatrix [] = inverse_2_target := by decide +kernel
theorem inverse_2 : wordGroup (inverse_lhs 2) = wordGroup (inverse_rhs 2) := by
  apply word_eq_of_matrix_eq
  exact inverse_2_left.trans inverse_2_right.symm

private def inverse_3_target : Mat := 1
private theorem inverse_3_left_s1 : wordMatrix [Atom.root 3 1] = atomMatrix (Atom.root 3 1) := by simp
private theorem inverse_3_left_s0 : wordMatrix [Atom.root 3 1, Atom.root 3 1] = inverse_3_target := by
  rw [wordMatrix_cons, inverse_3_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 3 1))
  decide +kernel
private theorem inverse_3_left : wordMatrix [Atom.root 3 1, Atom.root 3 1] = inverse_3_target := inverse_3_left_s0
private theorem inverse_3_right : wordMatrix [] = inverse_3_target := by decide +kernel
theorem inverse_3 : wordGroup (inverse_lhs 3) = wordGroup (inverse_rhs 3) := by
  apply word_eq_of_matrix_eq
  exact inverse_3_left.trans inverse_3_right.symm

private def inverse_4_target : Mat := 1
private theorem inverse_4_left_s2 : wordMatrix [Atom.root 10 1] = atomMatrix (Atom.root 10 1) := by simp
private def inverse_4_left_m1 : Mat := Sparse.eval (![[(0, e1)],
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
    [(3, e1), (11, e1)],
    [(1, e1), (7, e1), (12, e1)],
    [(1, e1), (7, e1), (13, e1)],
    [(8, e1), (14, e1)],
    [(6, e1), (15, e1)],
    [(16, e1)],
    [(0, e1), (3, e1), (11, e1), (17, e1)],
    [(7, e1), (12, e1), (13, e1), (18, e1)],
    [(10, e1), (19, e1)],
    [(2, e1), (6, e1), (15, e1), (20, e1)],
    [(21, e1)],
    [(14, e1), (22, e1)],
    [(5, e1), (10, e1), (19, e1), (23, e1)],
    [(1, e1), (7, e1), (18, e1), (24, e1)],
    [(8, e1), (14, e1), (22, e1), (25, e1)]])
private theorem inverse_4_left_s1 : wordMatrix [Atom.root 4 1, Atom.root 10 1] = inverse_4_left_m1 := by
  rw [wordMatrix_cons, inverse_4_left_s2]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 4 1))
  decide +kernel
private theorem inverse_4_left_s0 : wordMatrix [Atom.root 4 1, Atom.root 4 1, Atom.root 10 1] = inverse_4_target := by
  rw [wordMatrix_cons, inverse_4_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 4 1))
  decide +kernel
private theorem inverse_4_left : wordMatrix [Atom.root 4 1, Atom.root 4 1, Atom.root 10 1] = inverse_4_target := inverse_4_left_s0
private theorem inverse_4_right : wordMatrix [] = inverse_4_target := by decide +kernel
theorem inverse_4 : wordGroup (inverse_lhs 4) = wordGroup (inverse_rhs 4) := by
  apply word_eq_of_matrix_eq
  exact inverse_4_left.trans inverse_4_right.symm

private def inverse_5_target : Mat := 1
private theorem inverse_5_left_s1 : wordMatrix [Atom.root 5 1] = atomMatrix (Atom.root 5 1) := by simp
private theorem inverse_5_left_s0 : wordMatrix [Atom.root 5 1, Atom.root 5 1] = inverse_5_target := by
  rw [wordMatrix_cons, inverse_5_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 5 1))
  decide +kernel
private theorem inverse_5_left : wordMatrix [Atom.root 5 1, Atom.root 5 1] = inverse_5_target := inverse_5_left_s0
private theorem inverse_5_right : wordMatrix [] = inverse_5_target := by decide +kernel
theorem inverse_5 : wordGroup (inverse_lhs 5) = wordGroup (inverse_rhs 5) := by
  apply word_eq_of_matrix_eq
  exact inverse_5_left.trans inverse_5_right.symm

end Kourovka.Problem2153.WilsonModel.RootData.Relations
