import Kourovka.Problem2153.WilsonModel.RootData.Relations.Metadata
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
namespace Kourovka.Problem2153.WilsonModel.RootData.Relations
open Field8 F8
private def product_30_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(0, e2), (3, e1)],
    [(4, e1)],
    [(5, e1)],
    [(2, e2), (6, e1)],
    [(1, e6), (7, e1)],
    [(8, e1)],
    [(9, e1)],
    [(5, e2), (10, e1)],
    [(3, e6), (11, e1)],
    [(1, e7), (7, e2), (12, e1)],
    [(1, e7), (7, e2), (13, e1)],
    [(8, e2), (14, e1)],
    [(6, e6), (15, e1)],
    [(16, e1)],
    [(0, e5), (3, e7), (11, e2), (17, e1)],
    [(7, e4), (12, e2), (13, e2), (18, e1)],
    [(10, e6), (19, e1)],
    [(2, e5), (6, e7), (15, e2), (20, e1)],
    [(21, e1)],
    [(14, e6), (22, e1)],
    [(5, e5), (10, e7), (19, e2), (23, e1)],
    [(1, e3), (7, e5), (18, e6), (24, e1)],
    [(8, e5), (14, e7), (22, e2), (25, e1)]])
private theorem product_30_left_s1 : wordMatrix [Atom.root 4 3] = atomMatrix (Atom.root 4 3) := by simp
private theorem product_30_left_s0 : wordMatrix [Atom.root 4 1, Atom.root 4 3] = product_30_target := by
  rw [wordMatrix_cons, product_30_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 4 1))
  decide +kernel
private theorem product_30_left : wordMatrix [Atom.root 4 1, Atom.root 4 3] = product_30_target := product_30_left_s0
private theorem product_30_right_s1 : wordMatrix [Atom.root 10 7] = atomMatrix (Atom.root 10 7) := by simp
private theorem product_30_right_s0 : wordMatrix [Atom.root 4 2, Atom.root 10 7] = product_30_target := by
  rw [wordMatrix_cons, product_30_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 4 2))
  decide +kernel
private theorem product_30_right : wordMatrix [Atom.root 4 2, Atom.root 10 7] = product_30_target := product_30_right_s0
theorem product_30 : wordGroup (product_lhs 30) = wordGroup (product_rhs 30) := by
  apply word_eq_of_matrix_eq
  exact product_30_left.trans product_30_right.symm

private def product_31_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(0, e5), (3, e1)],
    [(4, e1)],
    [(5, e1)],
    [(2, e5), (6, e1)],
    [(1, e3), (7, e1)],
    [(8, e1)],
    [(9, e1)],
    [(5, e5), (10, e1)],
    [(0, e6), (3, e3), (11, e1)],
    [(1, e2), (7, e5), (12, e1)],
    [(1, e2), (7, e5), (13, e1)],
    [(8, e5), (14, e1)],
    [(2, e6), (6, e3), (15, e1)],
    [(16, e1)],
    [(0, e5), (3, e2), (11, e5), (17, e1)],
    [(1, e4), (7, e7), (12, e5), (13, e5), (18, e1)],
    [(5, e6), (10, e3), (19, e1)],
    [(2, e5), (6, e2), (15, e5), (20, e1)],
    [(21, e1)],
    [(8, e6), (14, e3), (22, e1)],
    [(5, e5), (10, e2), (19, e5), (23, e1)],
    [(1, e3), (7, e6), (12, e6), (13, e6), (18, e3), (24, e1)],
    [(8, e5), (14, e2), (22, e5), (25, e1)]])
private theorem product_31_left_s1 : wordMatrix [Atom.root 4 4] = atomMatrix (Atom.root 4 4) := by simp
private theorem product_31_left_s0 : wordMatrix [Atom.root 4 1, Atom.root 4 4] = product_31_target := by
  rw [wordMatrix_cons, product_31_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 4 1))
  decide +kernel
private theorem product_31_left : wordMatrix [Atom.root 4 1, Atom.root 4 4] = product_31_target := product_31_left_s0
private theorem product_31_right_s1 : wordMatrix [Atom.root 10 2] = atomMatrix (Atom.root 10 2) := by simp
private theorem product_31_right_s0 : wordMatrix [Atom.root 4 5, Atom.root 10 2] = product_31_target := by
  rw [wordMatrix_cons, product_31_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 4 5))
  decide +kernel
private theorem product_31_right : wordMatrix [Atom.root 4 5, Atom.root 10 2] = product_31_target := product_31_right_s0
theorem product_31 : wordGroup (product_lhs 31) = wordGroup (product_rhs 31) := by
  apply word_eq_of_matrix_eq
  exact product_31_left.trans product_31_right.symm

private def product_32_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(0, e4), (3, e1)],
    [(4, e1)],
    [(5, e1)],
    [(2, e4), (6, e1)],
    [(1, e2), (7, e1)],
    [(8, e1)],
    [(9, e1)],
    [(5, e4), (10, e1)],
    [(3, e2), (11, e1)],
    [(1, e3), (7, e4), (12, e1)],
    [(1, e3), (7, e4), (13, e1)],
    [(8, e4), (14, e1)],
    [(6, e2), (15, e1)],
    [(16, e1)],
    [(0, e7), (3, e3), (11, e4), (17, e1)],
    [(7, e6), (12, e4), (13, e4), (18, e1)],
    [(10, e2), (19, e1)],
    [(2, e7), (6, e3), (15, e4), (20, e1)],
    [(21, e1)],
    [(14, e2), (22, e1)],
    [(5, e7), (10, e3), (19, e4), (23, e1)],
    [(1, e5), (7, e7), (18, e2), (24, e1)],
    [(8, e7), (14, e3), (22, e4), (25, e1)]])
private theorem product_32_left_s1 : wordMatrix [Atom.root 4 5] = atomMatrix (Atom.root 4 5) := by simp
private theorem product_32_left_s0 : wordMatrix [Atom.root 4 1, Atom.root 4 5] = product_32_target := by
  rw [wordMatrix_cons, product_32_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 4 1))
  decide +kernel
private theorem product_32_left : wordMatrix [Atom.root 4 1, Atom.root 4 5] = product_32_target := product_32_left_s0
private theorem product_32_right_s1 : wordMatrix [Atom.root 10 3] = atomMatrix (Atom.root 10 3) := by simp
private theorem product_32_right_s0 : wordMatrix [Atom.root 4 4, Atom.root 10 3] = product_32_target := by
  rw [wordMatrix_cons, product_32_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 4 4))
  decide +kernel
private theorem product_32_right : wordMatrix [Atom.root 4 4, Atom.root 10 3] = product_32_target := product_32_right_s0
theorem product_32 : wordGroup (product_lhs 32) = wordGroup (product_rhs 32) := by
  apply word_eq_of_matrix_eq
  exact product_32_left.trans product_32_right.symm

private def product_33_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(0, e7), (3, e1)],
    [(4, e1)],
    [(5, e1)],
    [(2, e7), (6, e1)],
    [(1, e5), (7, e1)],
    [(8, e1)],
    [(9, e1)],
    [(5, e7), (10, e1)],
    [(0, e2), (3, e5), (11, e1)],
    [(1, e4), (7, e7), (12, e1)],
    [(1, e4), (7, e7), (13, e1)],
    [(8, e7), (14, e1)],
    [(2, e2), (6, e5), (15, e1)],
    [(16, e1)],
    [(0, e7), (3, e4), (11, e7), (17, e1)],
    [(1, e6), (7, e3), (12, e7), (13, e7), (18, e1)],
    [(5, e2), (10, e5), (19, e1)],
    [(2, e7), (6, e4), (15, e7), (20, e1)],
    [(21, e1)],
    [(8, e2), (14, e5), (22, e1)],
    [(5, e7), (10, e4), (19, e7), (23, e1)],
    [(1, e5), (7, e2), (12, e2), (13, e2), (18, e5), (24, e1)],
    [(8, e7), (14, e4), (22, e7), (25, e1)]])
private theorem product_33_left_s1 : wordMatrix [Atom.root 4 6] = atomMatrix (Atom.root 4 6) := by simp
private theorem product_33_left_s0 : wordMatrix [Atom.root 4 1, Atom.root 4 6] = product_33_target := by
  rw [wordMatrix_cons, product_33_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 4 1))
  decide +kernel
private theorem product_33_left : wordMatrix [Atom.root 4 1, Atom.root 4 6] = product_33_target := product_33_left_s0
private theorem product_33_right_s1 : wordMatrix [Atom.root 10 4] = atomMatrix (Atom.root 10 4) := by simp
private theorem product_33_right_s0 : wordMatrix [Atom.root 4 7, Atom.root 10 4] = product_33_target := by
  rw [wordMatrix_cons, product_33_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 4 7))
  decide +kernel
private theorem product_33_right : wordMatrix [Atom.root 4 7, Atom.root 10 4] = product_33_target := product_33_right_s0
theorem product_33 : wordGroup (product_lhs 33) = wordGroup (product_rhs 33) := by
  apply word_eq_of_matrix_eq
  exact product_33_left.trans product_33_right.symm

private def product_34_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(0, e6), (3, e1)],
    [(4, e1)],
    [(5, e1)],
    [(2, e6), (6, e1)],
    [(1, e4), (7, e1)],
    [(8, e1)],
    [(9, e1)],
    [(5, e6), (10, e1)],
    [(3, e4), (11, e1)],
    [(1, e5), (7, e6), (12, e1)],
    [(1, e5), (7, e6), (13, e1)],
    [(8, e6), (14, e1)],
    [(6, e4), (15, e1)],
    [(16, e1)],
    [(0, e3), (3, e5), (11, e6), (17, e1)],
    [(7, e2), (12, e6), (13, e6), (18, e1)],
    [(10, e4), (19, e1)],
    [(2, e3), (6, e5), (15, e6), (20, e1)],
    [(21, e1)],
    [(14, e4), (22, e1)],
    [(5, e3), (10, e5), (19, e6), (23, e1)],
    [(1, e7), (7, e3), (18, e4), (24, e1)],
    [(8, e3), (14, e5), (22, e6), (25, e1)]])
private theorem product_34_left_s1 : wordMatrix [Atom.root 4 7] = atomMatrix (Atom.root 4 7) := by simp
private theorem product_34_left_s0 : wordMatrix [Atom.root 4 1, Atom.root 4 7] = product_34_target := by
  rw [wordMatrix_cons, product_34_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 4 1))
  decide +kernel
private theorem product_34_left : wordMatrix [Atom.root 4 1, Atom.root 4 7] = product_34_target := product_34_left_s0
private theorem product_34_right_s1 : wordMatrix [Atom.root 10 5] = atomMatrix (Atom.root 10 5) := by simp
private theorem product_34_right_s0 : wordMatrix [Atom.root 4 6, Atom.root 10 5] = product_34_target := by
  rw [wordMatrix_cons, product_34_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 4 6))
  decide +kernel
private theorem product_34_right : wordMatrix [Atom.root 4 6, Atom.root 10 5] = product_34_target := product_34_right_s0
theorem product_34 : wordGroup (product_lhs 34) = wordGroup (product_rhs 34) := by
  apply word_eq_of_matrix_eq
  exact product_34_left.trans product_34_right.symm

private def product_35_target : Mat := 1
private theorem product_35_left_s1 : wordMatrix [Atom.root 5 1] = atomMatrix (Atom.root 5 1) := by simp
private theorem product_35_left_s0 : wordMatrix [Atom.root 5 1, Atom.root 5 1] = product_35_target := by
  rw [wordMatrix_cons, product_35_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 5 1))
  decide +kernel
private theorem product_35_left : wordMatrix [Atom.root 5 1, Atom.root 5 1] = product_35_target := product_35_left_s0
private theorem product_35_right : wordMatrix [] = product_35_target := by decide +kernel
theorem product_35 : wordGroup (product_lhs 35) = wordGroup (product_rhs 35) := by
  apply word_eq_of_matrix_eq
  exact product_35_left.trans product_35_right.symm

end Kourovka.Problem2153.WilsonModel.RootData.Relations
