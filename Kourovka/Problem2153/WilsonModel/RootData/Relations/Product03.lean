import Kourovka.Problem2153.WilsonModel.RootData.Relations.Metadata
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
namespace Kourovka.Problem2153.WilsonModel.RootData.Relations
open Field8 F8
private def product_18_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(0, e4), (2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(2, e2), (5, e1)],
    [(3, e4), (6, e1)],
    [(7, e1)],
    [(0, e7), (2, e3), (5, e4), (8, e1)],
    [(4, e2), (9, e1)],
    [(6, e2), (10, e1)],
    [(11, e1)],
    [(4, e3), (9, e4), (12, e1)],
    [(4, e3), (9, e4), (13, e1)],
    [(3, e7), (6, e3), (10, e4), (14, e1)],
    [(11, e4), (15, e1)],
    [(9, e6), (12, e4), (13, e4), (16, e1)],
    [(17, e1)],
    [(18, e1)],
    [(15, e2), (19, e1)],
    [(17, e4), (20, e1)],
    [(4, e5), (9, e7), (16, e2), (21, e1)],
    [(11, e7), (15, e3), (19, e4), (22, e1)],
    [(20, e2), (23, e1)],
    [(24, e1)],
    [(17, e7), (20, e3), (23, e4), (25, e1)]])
private theorem product_18_left_s1 : wordMatrix [Atom.root 2 5] = atomMatrix (Atom.root 2 5) := by simp
private theorem product_18_left_s0 : wordMatrix [Atom.root 2 1, Atom.root 2 5] = product_18_target := by
  rw [wordMatrix_cons, product_18_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 2 1))
  decide +kernel
private theorem product_18_left : wordMatrix [Atom.root 2 1, Atom.root 2 5] = product_18_target := product_18_left_s0
private theorem product_18_right_s1 : wordMatrix [Atom.root 7 3] = atomMatrix (Atom.root 7 3) := by simp
private theorem product_18_right_s0 : wordMatrix [Atom.root 2 4, Atom.root 7 3] = product_18_target := by
  rw [wordMatrix_cons, product_18_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 2 4))
  decide +kernel
private theorem product_18_right : wordMatrix [Atom.root 2 4, Atom.root 7 3] = product_18_target := product_18_right_s0
theorem product_18 : wordGroup (product_lhs 18) = wordGroup (product_rhs 18) := by
  apply word_eq_of_matrix_eq
  exact product_18_left.trans product_18_right.symm

private def product_19_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(0, e7), (2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(0, e2), (2, e5), (5, e1)],
    [(3, e7), (6, e1)],
    [(7, e1)],
    [(0, e7), (2, e4), (5, e7), (8, e1)],
    [(4, e5), (9, e1)],
    [(3, e2), (6, e5), (10, e1)],
    [(11, e1)],
    [(4, e4), (9, e7), (12, e1)],
    [(4, e4), (9, e7), (13, e1)],
    [(3, e7), (6, e4), (10, e7), (14, e1)],
    [(11, e7), (15, e1)],
    [(4, e6), (9, e3), (12, e7), (13, e7), (16, e1)],
    [(17, e1)],
    [(18, e1)],
    [(11, e2), (15, e5), (19, e1)],
    [(17, e7), (20, e1)],
    [(4, e5), (9, e2), (12, e2), (13, e2), (16, e5), (21, e1)],
    [(11, e7), (15, e4), (19, e7), (22, e1)],
    [(17, e2), (20, e5), (23, e1)],
    [(24, e1)],
    [(17, e7), (20, e4), (23, e7), (25, e1)]])
private theorem product_19_left_s1 : wordMatrix [Atom.root 2 6] = atomMatrix (Atom.root 2 6) := by simp
private theorem product_19_left_s0 : wordMatrix [Atom.root 2 1, Atom.root 2 6] = product_19_target := by
  rw [wordMatrix_cons, product_19_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 2 1))
  decide +kernel
private theorem product_19_left : wordMatrix [Atom.root 2 1, Atom.root 2 6] = product_19_target := product_19_left_s0
private theorem product_19_right_s1 : wordMatrix [Atom.root 7 4] = atomMatrix (Atom.root 7 4) := by simp
private theorem product_19_right_s0 : wordMatrix [Atom.root 2 7, Atom.root 7 4] = product_19_target := by
  rw [wordMatrix_cons, product_19_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 2 7))
  decide +kernel
private theorem product_19_right : wordMatrix [Atom.root 2 7, Atom.root 7 4] = product_19_target := product_19_right_s0
theorem product_19 : wordGroup (product_lhs 19) = wordGroup (product_rhs 19) := by
  apply word_eq_of_matrix_eq
  exact product_19_left.trans product_19_right.symm

private def product_20_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(0, e6), (2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(2, e4), (5, e1)],
    [(3, e6), (6, e1)],
    [(7, e1)],
    [(0, e3), (2, e5), (5, e6), (8, e1)],
    [(4, e4), (9, e1)],
    [(6, e4), (10, e1)],
    [(11, e1)],
    [(4, e5), (9, e6), (12, e1)],
    [(4, e5), (9, e6), (13, e1)],
    [(3, e3), (6, e5), (10, e6), (14, e1)],
    [(11, e6), (15, e1)],
    [(9, e2), (12, e6), (13, e6), (16, e1)],
    [(17, e1)],
    [(18, e1)],
    [(15, e4), (19, e1)],
    [(17, e6), (20, e1)],
    [(4, e7), (9, e3), (16, e4), (21, e1)],
    [(11, e3), (15, e5), (19, e6), (22, e1)],
    [(20, e4), (23, e1)],
    [(24, e1)],
    [(17, e3), (20, e5), (23, e6), (25, e1)]])
private theorem product_20_left_s1 : wordMatrix [Atom.root 2 7] = atomMatrix (Atom.root 2 7) := by simp
private theorem product_20_left_s0 : wordMatrix [Atom.root 2 1, Atom.root 2 7] = product_20_target := by
  rw [wordMatrix_cons, product_20_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 2 1))
  decide +kernel
private theorem product_20_left : wordMatrix [Atom.root 2 1, Atom.root 2 7] = product_20_target := product_20_left_s0
private theorem product_20_right_s1 : wordMatrix [Atom.root 7 5] = atomMatrix (Atom.root 7 5) := by simp
private theorem product_20_right_s0 : wordMatrix [Atom.root 2 6, Atom.root 7 5] = product_20_target := by
  rw [wordMatrix_cons, product_20_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 2 6))
  decide +kernel
private theorem product_20_right : wordMatrix [Atom.root 2 6, Atom.root 7 5] = product_20_target := product_20_right_s0
theorem product_20 : wordGroup (product_lhs 20) = wordGroup (product_rhs 20) := by
  apply word_eq_of_matrix_eq
  exact product_20_left.trans product_20_right.symm

private def product_21_target : Mat := 1
private theorem product_21_left_s1 : wordMatrix [Atom.root 3 1] = atomMatrix (Atom.root 3 1) := by simp
private theorem product_21_left_s0 : wordMatrix [Atom.root 3 1, Atom.root 3 1] = product_21_target := by
  rw [wordMatrix_cons, product_21_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 3 1))
  decide +kernel
private theorem product_21_left : wordMatrix [Atom.root 3 1, Atom.root 3 1] = product_21_target := product_21_left_s0
private theorem product_21_right : wordMatrix [] = product_21_target := by decide +kernel
theorem product_21 : wordGroup (product_lhs 21) = wordGroup (product_rhs 21) := by
  apply word_eq_of_matrix_eq
  exact product_21_left.trans product_21_right.symm

private def product_22_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(1, e3), (3, e1)],
    [(1, e7), (2, e3), (4, e1)],
    [(5, e1)],
    [(6, e1)],
    [(7, e1)],
    [(8, e1)],
    [(5, e3), (9, e1)],
    [(10, e1)],
    [(5, e7), (7, e3), (11, e1)],
    [(12, e1)],
    [(8, e3), (13, e1)],
    [(14, e1)],
    [(8, e7), (15, e1)],
    [(16, e1)],
    [(8, e5), (10, e7), (12, e3), (17, e1)],
    [(14, e3), (18, e1)],
    [(19, e1)],
    [(14, e7), (16, e3), (20, e1)],
    [(21, e1)],
    [(22, e1)],
    [(21, e3), (23, e1)],
    [(21, e7), (22, e3), (24, e1)],
    [(25, e1)]])
private theorem product_22_left_s1 : wordMatrix [Atom.root 3 2] = atomMatrix (Atom.root 3 2) := by simp
private theorem product_22_left_s0 : wordMatrix [Atom.root 3 1, Atom.root 3 2] = product_22_target := by
  rw [wordMatrix_cons, product_22_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 3 1))
  decide +kernel
private theorem product_22_left : wordMatrix [Atom.root 3 1, Atom.root 3 2] = product_22_target := product_22_left_s0
private theorem product_22_right_s0 : wordMatrix [Atom.root 3 3] = atomMatrix (Atom.root 3 3) := by simp
private theorem product_22_right : wordMatrix [Atom.root 3 3] = product_22_target := by
  rw [product_22_right_s0]
  decide +kernel
theorem product_22 : wordGroup (product_lhs 22) = wordGroup (product_rhs 22) := by
  apply word_eq_of_matrix_eq
  exact product_22_left.trans product_22_right.symm

private def product_23_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(1, e2), (3, e1)],
    [(1, e6), (2, e2), (4, e1)],
    [(5, e1)],
    [(6, e1)],
    [(7, e1)],
    [(8, e1)],
    [(5, e2), (9, e1)],
    [(10, e1)],
    [(5, e6), (7, e2), (11, e1)],
    [(12, e1)],
    [(8, e2), (13, e1)],
    [(14, e1)],
    [(8, e6), (15, e1)],
    [(16, e1)],
    [(8, e4), (10, e6), (12, e2), (17, e1)],
    [(14, e2), (18, e1)],
    [(19, e1)],
    [(14, e6), (16, e2), (20, e1)],
    [(21, e1)],
    [(22, e1)],
    [(21, e2), (23, e1)],
    [(21, e6), (22, e2), (24, e1)],
    [(25, e1)]])
private theorem product_23_left_s1 : wordMatrix [Atom.root 3 3] = atomMatrix (Atom.root 3 3) := by simp
private theorem product_23_left_s0 : wordMatrix [Atom.root 3 1, Atom.root 3 3] = product_23_target := by
  rw [wordMatrix_cons, product_23_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 3 1))
  decide +kernel
private theorem product_23_left : wordMatrix [Atom.root 3 1, Atom.root 3 3] = product_23_target := product_23_left_s0
private theorem product_23_right_s0 : wordMatrix [Atom.root 3 2] = atomMatrix (Atom.root 3 2) := by simp
private theorem product_23_right : wordMatrix [Atom.root 3 2] = product_23_target := by
  rw [product_23_right_s0]
  decide +kernel
theorem product_23 : wordGroup (product_lhs 23) = wordGroup (product_rhs 23) := by
  apply word_eq_of_matrix_eq
  exact product_23_left.trans product_23_right.symm

end Kourovka.Problem2153.WilsonModel.RootData.Relations
