import Kourovka.Problem2153.WilsonModel.RootData.Relations.Metadata
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
namespace Kourovka.Problem2153.WilsonModel.RootData.Relations
open Field8 F8
private def product_12_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(1, e7), (2, e1)],
    [(1, e2), (2, e5), (3, e1)],
    [(1, e7), (2, e4), (3, e7), (4, e1)],
    [(5, e1)],
    [(6, e1)],
    [(5, e7), (7, e1)],
    [(8, e1)],
    [(5, e2), (7, e5), (9, e1)],
    [(8, e5), (10, e1)],
    [(5, e7), (7, e4), (9, e7), (11, e1)],
    [(12, e1)],
    [(8, e4), (10, e7), (13, e1)],
    [(14, e1)],
    [(8, e6), (10, e3), (12, e7), (15, e1)],
    [(14, e7), (16, e1)],
    [(8, e5), (10, e2), (12, e2), (15, e5), (17, e1)],
    [(14, e2), (16, e5), (18, e1)],
    [(19, e1)],
    [(14, e7), (16, e4), (18, e7), (20, e1)],
    [(21, e1)],
    [(21, e7), (22, e1)],
    [(21, e2), (22, e5), (23, e1)],
    [(21, e7), (22, e4), (23, e7), (24, e1)],
    [(25, e1)]])
private theorem product_12_left_s1 : wordMatrix [Atom.root 1 6] = atomMatrix (Atom.root 1 6) := by simp
private theorem product_12_left_s0 : wordMatrix [Atom.root 1 1, Atom.root 1 6] = product_12_target := by
  rw [wordMatrix_cons, product_12_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 1 1))
  decide +kernel
private theorem product_12_left : wordMatrix [Atom.root 1 1, Atom.root 1 6] = product_12_target := product_12_left_s0
private theorem product_12_right_s1 : wordMatrix [Atom.root 3 4] = atomMatrix (Atom.root 3 4) := by simp
private theorem product_12_right_s0 : wordMatrix [Atom.root 1 7, Atom.root 3 4] = product_12_target := by
  rw [wordMatrix_cons, product_12_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 1 7))
  decide +kernel
private theorem product_12_right : wordMatrix [Atom.root 1 7, Atom.root 3 4] = product_12_target := product_12_right_s0
theorem product_12 : wordGroup (product_lhs 12) = wordGroup (product_rhs 12) := by
  apply word_eq_of_matrix_eq
  exact product_12_left.trans product_12_right.symm

private def product_13_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(1, e6), (2, e1)],
    [(2, e4), (3, e1)],
    [(1, e3), (2, e5), (3, e6), (4, e1)],
    [(5, e1)],
    [(6, e1)],
    [(5, e6), (7, e1)],
    [(8, e1)],
    [(7, e4), (9, e1)],
    [(8, e4), (10, e1)],
    [(5, e3), (7, e5), (9, e6), (11, e1)],
    [(12, e1)],
    [(8, e5), (10, e6), (13, e1)],
    [(14, e1)],
    [(10, e2), (12, e6), (15, e1)],
    [(14, e6), (16, e1)],
    [(8, e7), (10, e3), (15, e4), (17, e1)],
    [(16, e4), (18, e1)],
    [(19, e1)],
    [(14, e3), (16, e5), (18, e6), (20, e1)],
    [(21, e1)],
    [(21, e6), (22, e1)],
    [(22, e4), (23, e1)],
    [(21, e3), (22, e5), (23, e6), (24, e1)],
    [(25, e1)]])
private theorem product_13_left_s1 : wordMatrix [Atom.root 1 7] = atomMatrix (Atom.root 1 7) := by simp
private theorem product_13_left_s0 : wordMatrix [Atom.root 1 1, Atom.root 1 7] = product_13_target := by
  rw [wordMatrix_cons, product_13_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 1 1))
  decide +kernel
private theorem product_13_left : wordMatrix [Atom.root 1 1, Atom.root 1 7] = product_13_target := product_13_left_s0
private theorem product_13_right_s1 : wordMatrix [Atom.root 3 5] = atomMatrix (Atom.root 3 5) := by simp
private theorem product_13_right_s0 : wordMatrix [Atom.root 1 6, Atom.root 3 5] = product_13_target := by
  rw [wordMatrix_cons, product_13_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 1 6))
  decide +kernel
private theorem product_13_right : wordMatrix [Atom.root 1 6, Atom.root 3 5] = product_13_target := product_13_right_s0
theorem product_13 : wordGroup (product_lhs 13) = wordGroup (product_rhs 13) := by
  apply word_eq_of_matrix_eq
  exact product_13_left.trans product_13_right.symm

private def product_14_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(0, e1), (5, e1)],
    [(6, e1)],
    [(7, e1)],
    [(0, e1), (2, e1), (8, e1)],
    [(9, e1)],
    [(3, e1), (10, e1)],
    [(11, e1)],
    [(4, e1), (12, e1)],
    [(4, e1), (13, e1)],
    [(3, e1), (6, e1), (14, e1)],
    [(15, e1)],
    [(4, e1), (16, e1)],
    [(17, e1)],
    [(18, e1)],
    [(11, e1), (19, e1)],
    [(20, e1)],
    [(4, e1), (9, e1), (12, e1), (13, e1), (21, e1)],
    [(11, e1), (15, e1), (22, e1)],
    [(17, e1), (23, e1)],
    [(24, e1)],
    [(17, e1), (20, e1), (25, e1)]])
private theorem product_14_left_s1 : wordMatrix [Atom.root 2 1] = atomMatrix (Atom.root 2 1) := by simp
private theorem product_14_left_s0 : wordMatrix [Atom.root 2 1, Atom.root 2 1] = product_14_target := by
  rw [wordMatrix_cons, product_14_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 2 1))
  decide +kernel
private theorem product_14_left : wordMatrix [Atom.root 2 1, Atom.root 2 1] = product_14_target := product_14_left_s0
private theorem product_14_right_s0 : wordMatrix [Atom.root 7 1] = atomMatrix (Atom.root 7 1) := by simp
private theorem product_14_right : wordMatrix [Atom.root 7 1] = product_14_target := by
  rw [product_14_right_s0]
  decide +kernel
theorem product_14 : wordGroup (product_lhs 14) = wordGroup (product_rhs 14) := by
  apply word_eq_of_matrix_eq
  exact product_14_left.trans product_14_right.symm

private def product_15_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(0, e3), (2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(0, e4), (2, e7), (5, e1)],
    [(3, e3), (6, e1)],
    [(7, e1)],
    [(0, e3), (2, e6), (5, e3), (8, e1)],
    [(4, e7), (9, e1)],
    [(3, e4), (6, e7), (10, e1)],
    [(11, e1)],
    [(4, e6), (9, e3), (12, e1)],
    [(4, e6), (9, e3), (13, e1)],
    [(3, e3), (6, e6), (10, e3), (14, e1)],
    [(11, e3), (15, e1)],
    [(4, e2), (9, e5), (12, e3), (13, e3), (16, e1)],
    [(17, e1)],
    [(18, e1)],
    [(11, e4), (15, e7), (19, e1)],
    [(17, e3), (20, e1)],
    [(4, e7), (9, e4), (12, e4), (13, e4), (16, e7), (21, e1)],
    [(11, e3), (15, e6), (19, e3), (22, e1)],
    [(17, e4), (20, e7), (23, e1)],
    [(24, e1)],
    [(17, e3), (20, e6), (23, e3), (25, e1)]])
private theorem product_15_left_s1 : wordMatrix [Atom.root 2 2] = atomMatrix (Atom.root 2 2) := by simp
private theorem product_15_left_s0 : wordMatrix [Atom.root 2 1, Atom.root 2 2] = product_15_target := by
  rw [wordMatrix_cons, product_15_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 2 1))
  decide +kernel
private theorem product_15_left : wordMatrix [Atom.root 2 1, Atom.root 2 2] = product_15_target := product_15_left_s0
private theorem product_15_right_s1 : wordMatrix [Atom.root 7 6] = atomMatrix (Atom.root 7 6) := by simp
private theorem product_15_right_s0 : wordMatrix [Atom.root 2 3, Atom.root 7 6] = product_15_target := by
  rw [wordMatrix_cons, product_15_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 2 3))
  decide +kernel
private theorem product_15_right : wordMatrix [Atom.root 2 3, Atom.root 7 6] = product_15_target := product_15_right_s0
theorem product_15 : wordGroup (product_lhs 15) = wordGroup (product_rhs 15) := by
  apply word_eq_of_matrix_eq
  exact product_15_left.trans product_15_right.symm

private def product_16_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(0, e2), (2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(2, e6), (5, e1)],
    [(3, e2), (6, e1)],
    [(7, e1)],
    [(0, e5), (2, e7), (5, e2), (8, e1)],
    [(4, e6), (9, e1)],
    [(6, e6), (10, e1)],
    [(11, e1)],
    [(4, e7), (9, e2), (12, e1)],
    [(4, e7), (9, e2), (13, e1)],
    [(3, e5), (6, e7), (10, e2), (14, e1)],
    [(11, e2), (15, e1)],
    [(9, e4), (12, e2), (13, e2), (16, e1)],
    [(17, e1)],
    [(18, e1)],
    [(15, e6), (19, e1)],
    [(17, e2), (20, e1)],
    [(4, e3), (9, e5), (16, e6), (21, e1)],
    [(11, e5), (15, e7), (19, e2), (22, e1)],
    [(20, e6), (23, e1)],
    [(24, e1)],
    [(17, e5), (20, e7), (23, e2), (25, e1)]])
private theorem product_16_left_s1 : wordMatrix [Atom.root 2 3] = atomMatrix (Atom.root 2 3) := by simp
private theorem product_16_left_s0 : wordMatrix [Atom.root 2 1, Atom.root 2 3] = product_16_target := by
  rw [wordMatrix_cons, product_16_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 2 1))
  decide +kernel
private theorem product_16_left : wordMatrix [Atom.root 2 1, Atom.root 2 3] = product_16_target := product_16_left_s0
private theorem product_16_right_s1 : wordMatrix [Atom.root 7 7] = atomMatrix (Atom.root 7 7) := by simp
private theorem product_16_right_s0 : wordMatrix [Atom.root 2 2, Atom.root 7 7] = product_16_target := by
  rw [wordMatrix_cons, product_16_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 2 2))
  decide +kernel
private theorem product_16_right : wordMatrix [Atom.root 2 2, Atom.root 7 7] = product_16_target := product_16_right_s0
theorem product_16 : wordGroup (product_lhs 16) = wordGroup (product_rhs 16) := by
  apply word_eq_of_matrix_eq
  exact product_16_left.trans product_16_right.symm

private def product_17_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(0, e5), (2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(0, e6), (2, e3), (5, e1)],
    [(3, e5), (6, e1)],
    [(7, e1)],
    [(0, e5), (2, e2), (5, e5), (8, e1)],
    [(4, e3), (9, e1)],
    [(3, e6), (6, e3), (10, e1)],
    [(11, e1)],
    [(4, e2), (9, e5), (12, e1)],
    [(4, e2), (9, e5), (13, e1)],
    [(3, e5), (6, e2), (10, e5), (14, e1)],
    [(11, e5), (15, e1)],
    [(4, e4), (9, e7), (12, e5), (13, e5), (16, e1)],
    [(17, e1)],
    [(18, e1)],
    [(11, e6), (15, e3), (19, e1)],
    [(17, e5), (20, e1)],
    [(4, e3), (9, e6), (12, e6), (13, e6), (16, e3), (21, e1)],
    [(11, e5), (15, e2), (19, e5), (22, e1)],
    [(17, e6), (20, e3), (23, e1)],
    [(24, e1)],
    [(17, e5), (20, e2), (23, e5), (25, e1)]])
private theorem product_17_left_s1 : wordMatrix [Atom.root 2 4] = atomMatrix (Atom.root 2 4) := by simp
private theorem product_17_left_s0 : wordMatrix [Atom.root 2 1, Atom.root 2 4] = product_17_target := by
  rw [wordMatrix_cons, product_17_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 2 1))
  decide +kernel
private theorem product_17_left : wordMatrix [Atom.root 2 1, Atom.root 2 4] = product_17_target := product_17_left_s0
private theorem product_17_right_s1 : wordMatrix [Atom.root 7 2] = atomMatrix (Atom.root 7 2) := by simp
private theorem product_17_right_s0 : wordMatrix [Atom.root 2 5, Atom.root 7 2] = product_17_target := by
  rw [wordMatrix_cons, product_17_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 2 5))
  decide +kernel
private theorem product_17_right : wordMatrix [Atom.root 2 5, Atom.root 7 2] = product_17_target := product_17_right_s0
theorem product_17 : wordGroup (product_lhs 17) = wordGroup (product_rhs 17) := by
  apply word_eq_of_matrix_eq
  exact product_17_left.trans product_17_right.symm

end Kourovka.Problem2153.WilsonModel.RootData.Relations
