import Kourovka.Problem2153.WilsonModel.RootData.Relations.Metadata
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
namespace Kourovka.Problem2153.WilsonModel.RootData.Relations
open Field8 F8
private def product_6_target : Mat := Sparse.eval (![[(0, e1)],
    [(0, e6), (1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(3, e4), (5, e1)],
    [(4, e6), (6, e1)],
    [(4, e4), (7, e1)],
    [(4, e5), (6, e4), (7, e6), (8, e1)],
    [(9, e1)],
    [(9, e6), (10, e1)],
    [(11, e1)],
    [(11, e6), (12, e1)],
    [(13, e1)],
    [(11, e2), (13, e6), (14, e1)],
    [(15, e1)],
    [(15, e6), (16, e1)],
    [(17, e1)],
    [(17, e6), (18, e1)],
    [(17, e4), (19, e1)],
    [(20, e1)],
    [(17, e5), (18, e4), (19, e6), (21, e1)],
    [(20, e4), (22, e1)],
    [(23, e1)],
    [(24, e1)],
    [(24, e6), (25, e1)]])
private theorem product_6_left_s1 : wordMatrix [Atom.root 0 7] = atomMatrix (Atom.root 0 7) := by simp
private theorem product_6_left_s0 : wordMatrix [Atom.root 0 1, Atom.root 0 7] = product_6_target := by
  rw [wordMatrix_cons, product_6_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 0 1))
  decide +kernel
private theorem product_6_left : wordMatrix [Atom.root 0 1, Atom.root 0 7] = product_6_target := product_6_left_s0
private theorem product_6_right_s0 : wordMatrix [Atom.root 0 6] = atomMatrix (Atom.root 0 6) := by simp
private theorem product_6_right : wordMatrix [Atom.root 0 6] = product_6_target := by
  rw [product_6_right_s0]
  decide +kernel
theorem product_6 : wordGroup (product_lhs 6) = wordGroup (product_rhs 6) := by
  apply word_eq_of_matrix_eq
  exact product_6_left.trans product_6_right.symm

private def product_7_target : Mat := Sparse.eval (![[(0, e1)],
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
private theorem product_7_left_s1 : wordMatrix [Atom.root 1 1] = atomMatrix (Atom.root 1 1) := by simp
private theorem product_7_left_s0 : wordMatrix [Atom.root 1 1, Atom.root 1 1] = product_7_target := by
  rw [wordMatrix_cons, product_7_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 1 1))
  decide +kernel
private theorem product_7_left : wordMatrix [Atom.root 1 1, Atom.root 1 1] = product_7_target := product_7_left_s0
private theorem product_7_right_s0 : wordMatrix [Atom.root 3 1] = atomMatrix (Atom.root 3 1) := by simp
private theorem product_7_right : wordMatrix [Atom.root 3 1] = product_7_target := by
  rw [product_7_right_s0]
  decide +kernel
theorem product_7 : wordGroup (product_lhs 7) = wordGroup (product_rhs 7) := by
  apply word_eq_of_matrix_eq
  exact product_7_left.trans product_7_right.symm

private def product_8_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(1, e3), (2, e1)],
    [(1, e4), (2, e7), (3, e1)],
    [(1, e3), (2, e6), (3, e3), (4, e1)],
    [(5, e1)],
    [(6, e1)],
    [(5, e3), (7, e1)],
    [(8, e1)],
    [(5, e4), (7, e7), (9, e1)],
    [(8, e7), (10, e1)],
    [(5, e3), (7, e6), (9, e3), (11, e1)],
    [(12, e1)],
    [(8, e6), (10, e3), (13, e1)],
    [(14, e1)],
    [(8, e2), (10, e5), (12, e3), (15, e1)],
    [(14, e3), (16, e1)],
    [(8, e7), (10, e4), (12, e4), (15, e7), (17, e1)],
    [(14, e4), (16, e7), (18, e1)],
    [(19, e1)],
    [(14, e3), (16, e6), (18, e3), (20, e1)],
    [(21, e1)],
    [(21, e3), (22, e1)],
    [(21, e4), (22, e7), (23, e1)],
    [(21, e3), (22, e6), (23, e3), (24, e1)],
    [(25, e1)]])
private theorem product_8_left_s1 : wordMatrix [Atom.root 1 2] = atomMatrix (Atom.root 1 2) := by simp
private theorem product_8_left_s0 : wordMatrix [Atom.root 1 1, Atom.root 1 2] = product_8_target := by
  rw [wordMatrix_cons, product_8_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 1 1))
  decide +kernel
private theorem product_8_left : wordMatrix [Atom.root 1 1, Atom.root 1 2] = product_8_target := product_8_left_s0
private theorem product_8_right_s1 : wordMatrix [Atom.root 3 6] = atomMatrix (Atom.root 3 6) := by simp
private theorem product_8_right_s0 : wordMatrix [Atom.root 1 3, Atom.root 3 6] = product_8_target := by
  rw [wordMatrix_cons, product_8_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 1 3))
  decide +kernel
private theorem product_8_right : wordMatrix [Atom.root 1 3, Atom.root 3 6] = product_8_target := product_8_right_s0
theorem product_8 : wordGroup (product_lhs 8) = wordGroup (product_rhs 8) := by
  apply word_eq_of_matrix_eq
  exact product_8_left.trans product_8_right.symm

private def product_9_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(1, e2), (2, e1)],
    [(2, e6), (3, e1)],
    [(1, e5), (2, e7), (3, e2), (4, e1)],
    [(5, e1)],
    [(6, e1)],
    [(5, e2), (7, e1)],
    [(8, e1)],
    [(7, e6), (9, e1)],
    [(8, e6), (10, e1)],
    [(5, e5), (7, e7), (9, e2), (11, e1)],
    [(12, e1)],
    [(8, e7), (10, e2), (13, e1)],
    [(14, e1)],
    [(10, e4), (12, e2), (15, e1)],
    [(14, e2), (16, e1)],
    [(8, e3), (10, e5), (15, e6), (17, e1)],
    [(16, e6), (18, e1)],
    [(19, e1)],
    [(14, e5), (16, e7), (18, e2), (20, e1)],
    [(21, e1)],
    [(21, e2), (22, e1)],
    [(22, e6), (23, e1)],
    [(21, e5), (22, e7), (23, e2), (24, e1)],
    [(25, e1)]])
private theorem product_9_left_s1 : wordMatrix [Atom.root 1 3] = atomMatrix (Atom.root 1 3) := by simp
private theorem product_9_left_s0 : wordMatrix [Atom.root 1 1, Atom.root 1 3] = product_9_target := by
  rw [wordMatrix_cons, product_9_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 1 1))
  decide +kernel
private theorem product_9_left : wordMatrix [Atom.root 1 1, Atom.root 1 3] = product_9_target := product_9_left_s0
private theorem product_9_right_s1 : wordMatrix [Atom.root 3 7] = atomMatrix (Atom.root 3 7) := by simp
private theorem product_9_right_s0 : wordMatrix [Atom.root 1 2, Atom.root 3 7] = product_9_target := by
  rw [wordMatrix_cons, product_9_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 1 2))
  decide +kernel
private theorem product_9_right : wordMatrix [Atom.root 1 2, Atom.root 3 7] = product_9_target := product_9_right_s0
theorem product_9 : wordGroup (product_lhs 9) = wordGroup (product_rhs 9) := by
  apply word_eq_of_matrix_eq
  exact product_9_left.trans product_9_right.symm

private def product_10_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(1, e5), (2, e1)],
    [(1, e6), (2, e3), (3, e1)],
    [(1, e5), (2, e2), (3, e5), (4, e1)],
    [(5, e1)],
    [(6, e1)],
    [(5, e5), (7, e1)],
    [(8, e1)],
    [(5, e6), (7, e3), (9, e1)],
    [(8, e3), (10, e1)],
    [(5, e5), (7, e2), (9, e5), (11, e1)],
    [(12, e1)],
    [(8, e2), (10, e5), (13, e1)],
    [(14, e1)],
    [(8, e4), (10, e7), (12, e5), (15, e1)],
    [(14, e5), (16, e1)],
    [(8, e3), (10, e6), (12, e6), (15, e3), (17, e1)],
    [(14, e6), (16, e3), (18, e1)],
    [(19, e1)],
    [(14, e5), (16, e2), (18, e5), (20, e1)],
    [(21, e1)],
    [(21, e5), (22, e1)],
    [(21, e6), (22, e3), (23, e1)],
    [(21, e5), (22, e2), (23, e5), (24, e1)],
    [(25, e1)]])
private theorem product_10_left_s1 : wordMatrix [Atom.root 1 4] = atomMatrix (Atom.root 1 4) := by simp
private theorem product_10_left_s0 : wordMatrix [Atom.root 1 1, Atom.root 1 4] = product_10_target := by
  rw [wordMatrix_cons, product_10_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 1 1))
  decide +kernel
private theorem product_10_left : wordMatrix [Atom.root 1 1, Atom.root 1 4] = product_10_target := product_10_left_s0
private theorem product_10_right_s1 : wordMatrix [Atom.root 3 2] = atomMatrix (Atom.root 3 2) := by simp
private theorem product_10_right_s0 : wordMatrix [Atom.root 1 5, Atom.root 3 2] = product_10_target := by
  rw [wordMatrix_cons, product_10_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 1 5))
  decide +kernel
private theorem product_10_right : wordMatrix [Atom.root 1 5, Atom.root 3 2] = product_10_target := product_10_right_s0
theorem product_10 : wordGroup (product_lhs 10) = wordGroup (product_rhs 10) := by
  apply word_eq_of_matrix_eq
  exact product_10_left.trans product_10_right.symm

private def product_11_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(1, e4), (2, e1)],
    [(2, e2), (3, e1)],
    [(1, e7), (2, e3), (3, e4), (4, e1)],
    [(5, e1)],
    [(6, e1)],
    [(5, e4), (7, e1)],
    [(8, e1)],
    [(7, e2), (9, e1)],
    [(8, e2), (10, e1)],
    [(5, e7), (7, e3), (9, e4), (11, e1)],
    [(12, e1)],
    [(8, e3), (10, e4), (13, e1)],
    [(14, e1)],
    [(10, e6), (12, e4), (15, e1)],
    [(14, e4), (16, e1)],
    [(8, e5), (10, e7), (15, e2), (17, e1)],
    [(16, e2), (18, e1)],
    [(19, e1)],
    [(14, e7), (16, e3), (18, e4), (20, e1)],
    [(21, e1)],
    [(21, e4), (22, e1)],
    [(22, e2), (23, e1)],
    [(21, e7), (22, e3), (23, e4), (24, e1)],
    [(25, e1)]])
private theorem product_11_left_s1 : wordMatrix [Atom.root 1 5] = atomMatrix (Atom.root 1 5) := by simp
private theorem product_11_left_s0 : wordMatrix [Atom.root 1 1, Atom.root 1 5] = product_11_target := by
  rw [wordMatrix_cons, product_11_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 1 1))
  decide +kernel
private theorem product_11_left : wordMatrix [Atom.root 1 1, Atom.root 1 5] = product_11_target := product_11_left_s0
private theorem product_11_right_s1 : wordMatrix [Atom.root 3 3] = atomMatrix (Atom.root 3 3) := by simp
private theorem product_11_right_s0 : wordMatrix [Atom.root 1 4, Atom.root 3 3] = product_11_target := by
  rw [wordMatrix_cons, product_11_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 1 4))
  decide +kernel
private theorem product_11_right : wordMatrix [Atom.root 1 4, Atom.root 3 3] = product_11_target := product_11_right_s0
theorem product_11 : wordGroup (product_lhs 11) = wordGroup (product_rhs 11) := by
  apply word_eq_of_matrix_eq
  exact product_11_left.trans product_11_right.symm

end Kourovka.Problem2153.WilsonModel.RootData.Relations
