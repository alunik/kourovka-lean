import Kourovka.Problem2153.WilsonModel.RootData.Relations.Metadata
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
namespace Kourovka.Problem2153.WilsonModel.RootData.Relations
open Field8 F8
private def product_24_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(1, e5), (3, e1)],
    [(1, e3), (2, e5), (4, e1)],
    [(5, e1)],
    [(6, e1)],
    [(7, e1)],
    [(8, e1)],
    [(5, e5), (9, e1)],
    [(10, e1)],
    [(5, e3), (7, e5), (11, e1)],
    [(12, e1)],
    [(8, e5), (13, e1)],
    [(14, e1)],
    [(8, e3), (15, e1)],
    [(16, e1)],
    [(8, e7), (10, e3), (12, e5), (17, e1)],
    [(14, e5), (18, e1)],
    [(19, e1)],
    [(14, e3), (16, e5), (20, e1)],
    [(21, e1)],
    [(22, e1)],
    [(21, e5), (23, e1)],
    [(21, e3), (22, e5), (24, e1)],
    [(25, e1)]])
private theorem product_24_left_s1 : wordMatrix [Atom.root 3 4] = atomMatrix (Atom.root 3 4) := by simp
private theorem product_24_left_s0 : wordMatrix [Atom.root 3 1, Atom.root 3 4] = product_24_target := by
  rw [wordMatrix_cons, product_24_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 3 1))
  decide +kernel
private theorem product_24_left : wordMatrix [Atom.root 3 1, Atom.root 3 4] = product_24_target := product_24_left_s0
private theorem product_24_right_s0 : wordMatrix [Atom.root 3 5] = atomMatrix (Atom.root 3 5) := by simp
private theorem product_24_right : wordMatrix [Atom.root 3 5] = product_24_target := by
  rw [product_24_right_s0]
  decide +kernel
theorem product_24 : wordGroup (product_lhs 24) = wordGroup (product_rhs 24) := by
  apply word_eq_of_matrix_eq
  exact product_24_left.trans product_24_right.symm

private def product_25_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(1, e4), (3, e1)],
    [(1, e2), (2, e4), (4, e1)],
    [(5, e1)],
    [(6, e1)],
    [(7, e1)],
    [(8, e1)],
    [(5, e4), (9, e1)],
    [(10, e1)],
    [(5, e2), (7, e4), (11, e1)],
    [(12, e1)],
    [(8, e4), (13, e1)],
    [(14, e1)],
    [(8, e2), (15, e1)],
    [(16, e1)],
    [(8, e6), (10, e2), (12, e4), (17, e1)],
    [(14, e4), (18, e1)],
    [(19, e1)],
    [(14, e2), (16, e4), (20, e1)],
    [(21, e1)],
    [(22, e1)],
    [(21, e4), (23, e1)],
    [(21, e2), (22, e4), (24, e1)],
    [(25, e1)]])
private theorem product_25_left_s1 : wordMatrix [Atom.root 3 5] = atomMatrix (Atom.root 3 5) := by simp
private theorem product_25_left_s0 : wordMatrix [Atom.root 3 1, Atom.root 3 5] = product_25_target := by
  rw [wordMatrix_cons, product_25_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 3 1))
  decide +kernel
private theorem product_25_left : wordMatrix [Atom.root 3 1, Atom.root 3 5] = product_25_target := product_25_left_s0
private theorem product_25_right_s0 : wordMatrix [Atom.root 3 4] = atomMatrix (Atom.root 3 4) := by simp
private theorem product_25_right : wordMatrix [Atom.root 3 4] = product_25_target := by
  rw [product_25_right_s0]
  decide +kernel
theorem product_25 : wordGroup (product_lhs 25) = wordGroup (product_rhs 25) := by
  apply word_eq_of_matrix_eq
  exact product_25_left.trans product_25_right.symm

private def product_26_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(1, e7), (3, e1)],
    [(1, e5), (2, e7), (4, e1)],
    [(5, e1)],
    [(6, e1)],
    [(7, e1)],
    [(8, e1)],
    [(5, e7), (9, e1)],
    [(10, e1)],
    [(5, e5), (7, e7), (11, e1)],
    [(12, e1)],
    [(8, e7), (13, e1)],
    [(14, e1)],
    [(8, e5), (15, e1)],
    [(16, e1)],
    [(8, e3), (10, e5), (12, e7), (17, e1)],
    [(14, e7), (18, e1)],
    [(19, e1)],
    [(14, e5), (16, e7), (20, e1)],
    [(21, e1)],
    [(22, e1)],
    [(21, e7), (23, e1)],
    [(21, e5), (22, e7), (24, e1)],
    [(25, e1)]])
private theorem product_26_left_s1 : wordMatrix [Atom.root 3 6] = atomMatrix (Atom.root 3 6) := by simp
private theorem product_26_left_s0 : wordMatrix [Atom.root 3 1, Atom.root 3 6] = product_26_target := by
  rw [wordMatrix_cons, product_26_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 3 1))
  decide +kernel
private theorem product_26_left : wordMatrix [Atom.root 3 1, Atom.root 3 6] = product_26_target := product_26_left_s0
private theorem product_26_right_s0 : wordMatrix [Atom.root 3 7] = atomMatrix (Atom.root 3 7) := by simp
private theorem product_26_right : wordMatrix [Atom.root 3 7] = product_26_target := by
  rw [product_26_right_s0]
  decide +kernel
theorem product_26 : wordGroup (product_lhs 26) = wordGroup (product_rhs 26) := by
  apply word_eq_of_matrix_eq
  exact product_26_left.trans product_26_right.symm

private def product_27_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(1, e6), (3, e1)],
    [(1, e4), (2, e6), (4, e1)],
    [(5, e1)],
    [(6, e1)],
    [(7, e1)],
    [(8, e1)],
    [(5, e6), (9, e1)],
    [(10, e1)],
    [(5, e4), (7, e6), (11, e1)],
    [(12, e1)],
    [(8, e6), (13, e1)],
    [(14, e1)],
    [(8, e4), (15, e1)],
    [(16, e1)],
    [(8, e2), (10, e4), (12, e6), (17, e1)],
    [(14, e6), (18, e1)],
    [(19, e1)],
    [(14, e4), (16, e6), (20, e1)],
    [(21, e1)],
    [(22, e1)],
    [(21, e6), (23, e1)],
    [(21, e4), (22, e6), (24, e1)],
    [(25, e1)]])
private theorem product_27_left_s1 : wordMatrix [Atom.root 3 7] = atomMatrix (Atom.root 3 7) := by simp
private theorem product_27_left_s0 : wordMatrix [Atom.root 3 1, Atom.root 3 7] = product_27_target := by
  rw [wordMatrix_cons, product_27_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 3 1))
  decide +kernel
private theorem product_27_left : wordMatrix [Atom.root 3 1, Atom.root 3 7] = product_27_target := product_27_left_s0
private theorem product_27_right_s0 : wordMatrix [Atom.root 3 6] = atomMatrix (Atom.root 3 6) := by simp
private theorem product_27_right : wordMatrix [Atom.root 3 6] = product_27_target := by
  rw [product_27_right_s0]
  decide +kernel
theorem product_27 : wordGroup (product_lhs 27) = wordGroup (product_rhs 27) := by
  apply word_eq_of_matrix_eq
  exact product_27_left.trans product_27_right.symm

private def product_28_target : Mat := Sparse.eval (![[(0, e1)],
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
private theorem product_28_left_s1 : wordMatrix [Atom.root 4 1] = atomMatrix (Atom.root 4 1) := by simp
private theorem product_28_left_s0 : wordMatrix [Atom.root 4 1, Atom.root 4 1] = product_28_target := by
  rw [wordMatrix_cons, product_28_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 4 1))
  decide +kernel
private theorem product_28_left : wordMatrix [Atom.root 4 1, Atom.root 4 1] = product_28_target := product_28_left_s0
private theorem product_28_right_s0 : wordMatrix [Atom.root 10 1] = atomMatrix (Atom.root 10 1) := by simp
private theorem product_28_right : wordMatrix [Atom.root 10 1] = product_28_target := by
  rw [product_28_right_s0]
  decide +kernel
theorem product_28 : wordGroup (product_lhs 28) = wordGroup (product_rhs 28) := by
  apply word_eq_of_matrix_eq
  exact product_28_left.trans product_28_right.symm

private def product_29_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(0, e3), (3, e1)],
    [(4, e1)],
    [(5, e1)],
    [(2, e3), (6, e1)],
    [(1, e7), (7, e1)],
    [(8, e1)],
    [(9, e1)],
    [(5, e3), (10, e1)],
    [(0, e4), (3, e7), (11, e1)],
    [(1, e6), (7, e3), (12, e1)],
    [(1, e6), (7, e3), (13, e1)],
    [(8, e3), (14, e1)],
    [(2, e4), (6, e7), (15, e1)],
    [(16, e1)],
    [(0, e3), (3, e6), (11, e3), (17, e1)],
    [(1, e2), (7, e5), (12, e3), (13, e3), (18, e1)],
    [(5, e4), (10, e7), (19, e1)],
    [(2, e3), (6, e6), (15, e3), (20, e1)],
    [(21, e1)],
    [(8, e4), (14, e7), (22, e1)],
    [(5, e3), (10, e6), (19, e3), (23, e1)],
    [(1, e7), (7, e4), (12, e4), (13, e4), (18, e7), (24, e1)],
    [(8, e3), (14, e6), (22, e3), (25, e1)]])
private theorem product_29_left_s1 : wordMatrix [Atom.root 4 2] = atomMatrix (Atom.root 4 2) := by simp
private theorem product_29_left_s0 : wordMatrix [Atom.root 4 1, Atom.root 4 2] = product_29_target := by
  rw [wordMatrix_cons, product_29_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 4 1))
  decide +kernel
private theorem product_29_left : wordMatrix [Atom.root 4 1, Atom.root 4 2] = product_29_target := product_29_left_s0
private theorem product_29_right_s1 : wordMatrix [Atom.root 10 6] = atomMatrix (Atom.root 10 6) := by simp
private theorem product_29_right_s0 : wordMatrix [Atom.root 4 3, Atom.root 10 6] = product_29_target := by
  rw [wordMatrix_cons, product_29_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 4 3))
  decide +kernel
private theorem product_29_right : wordMatrix [Atom.root 4 3, Atom.root 10 6] = product_29_target := product_29_right_s0
theorem product_29 : wordGroup (product_lhs 29) = wordGroup (product_rhs 29) := by
  apply word_eq_of_matrix_eq
  exact product_29_left.trans product_29_right.symm

end Kourovka.Problem2153.WilsonModel.RootData.Relations
