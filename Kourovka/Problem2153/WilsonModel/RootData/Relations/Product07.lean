import Kourovka.Problem2153.WilsonModel.RootData.Relations.Metadata
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
namespace Kourovka.Problem2153.WilsonModel.RootData.Relations
open Field8 F8
private def product_42_target : Mat := Sparse.eval (![[(0, e1)],
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
private theorem product_42_left_s1 : wordMatrix [Atom.root 6 1] = atomMatrix (Atom.root 6 1) := by simp
private theorem product_42_left_s0 : wordMatrix [Atom.root 6 1, Atom.root 6 1] = product_42_target := by
  rw [wordMatrix_cons, product_42_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 6 1))
  decide +kernel
private theorem product_42_left : wordMatrix [Atom.root 6 1, Atom.root 6 1] = product_42_target := product_42_left_s0
private theorem product_42_right_s0 : wordMatrix [Atom.root 11 1] = atomMatrix (Atom.root 11 1) := by simp
private theorem product_42_right : wordMatrix [Atom.root 11 1] = product_42_target := by
  rw [product_42_right_s0]
  decide +kernel
theorem product_42 : wordGroup (product_lhs 42) = wordGroup (product_rhs 42) := by
  apply word_eq_of_matrix_eq
  exact product_42_left.trans product_42_right.symm

private def product_43_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(1, e3), (5, e1)],
    [(0, e7), (6, e1)],
    [(2, e3), (7, e1)],
    [(8, e1)],
    [(3, e3), (9, e1)],
    [(10, e1)],
    [(4, e3), (11, e1)],
    [(12, e1)],
    [(0, e6), (6, e3), (13, e1)],
    [(1, e4), (5, e7), (14, e1)],
    [(15, e1)],
    [(2, e4), (7, e7), (16, e1)],
    [(17, e1)],
    [(3, e4), (9, e7), (18, e1)],
    [(0, e2), (6, e5), (12, e3), (19, e1)],
    [(4, e4), (11, e7), (20, e1)],
    [(1, e3), (5, e6), (14, e3), (21, e1)],
    [(2, e3), (7, e6), (16, e3), (22, e1)],
    [(3, e3), (9, e6), (18, e3), (23, e1)],
    [(4, e3), (11, e6), (20, e3), (24, e1)],
    [(0, e7), (6, e4), (12, e4), (19, e7), (25, e1)]])
private theorem product_43_left_s1 : wordMatrix [Atom.root 6 2] = atomMatrix (Atom.root 6 2) := by simp
private theorem product_43_left_s0 : wordMatrix [Atom.root 6 1, Atom.root 6 2] = product_43_target := by
  rw [wordMatrix_cons, product_43_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 6 1))
  decide +kernel
private theorem product_43_left : wordMatrix [Atom.root 6 1, Atom.root 6 2] = product_43_target := product_43_left_s0
private theorem product_43_right_s1 : wordMatrix [Atom.root 11 6] = atomMatrix (Atom.root 11 6) := by simp
private theorem product_43_right_s0 : wordMatrix [Atom.root 6 3, Atom.root 11 6] = product_43_target := by
  rw [wordMatrix_cons, product_43_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 6 3))
  decide +kernel
private theorem product_43_right : wordMatrix [Atom.root 6 3, Atom.root 11 6] = product_43_target := product_43_right_s0
theorem product_43 : wordGroup (product_lhs 43) = wordGroup (product_rhs 43) := by
  apply word_eq_of_matrix_eq
  exact product_43_left.trans product_43_right.symm

private def product_44_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(1, e2), (5, e1)],
    [(0, e6), (6, e1)],
    [(2, e2), (7, e1)],
    [(8, e1)],
    [(3, e2), (9, e1)],
    [(10, e1)],
    [(4, e2), (11, e1)],
    [(12, e1)],
    [(0, e7), (6, e2), (13, e1)],
    [(5, e6), (14, e1)],
    [(15, e1)],
    [(7, e6), (16, e1)],
    [(17, e1)],
    [(9, e6), (18, e1)],
    [(6, e4), (12, e2), (19, e1)],
    [(11, e6), (20, e1)],
    [(1, e5), (5, e7), (14, e2), (21, e1)],
    [(2, e5), (7, e7), (16, e2), (22, e1)],
    [(3, e5), (9, e7), (18, e2), (23, e1)],
    [(4, e5), (11, e7), (20, e2), (24, e1)],
    [(0, e3), (6, e5), (19, e6), (25, e1)]])
private theorem product_44_left_s1 : wordMatrix [Atom.root 6 3] = atomMatrix (Atom.root 6 3) := by simp
private theorem product_44_left_s0 : wordMatrix [Atom.root 6 1, Atom.root 6 3] = product_44_target := by
  rw [wordMatrix_cons, product_44_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 6 1))
  decide +kernel
private theorem product_44_left : wordMatrix [Atom.root 6 1, Atom.root 6 3] = product_44_target := product_44_left_s0
private theorem product_44_right_s1 : wordMatrix [Atom.root 11 7] = atomMatrix (Atom.root 11 7) := by simp
private theorem product_44_right_s0 : wordMatrix [Atom.root 6 2, Atom.root 11 7] = product_44_target := by
  rw [wordMatrix_cons, product_44_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 6 2))
  decide +kernel
private theorem product_44_right : wordMatrix [Atom.root 6 2, Atom.root 11 7] = product_44_target := product_44_right_s0
theorem product_44 : wordGroup (product_lhs 44) = wordGroup (product_rhs 44) := by
  apply word_eq_of_matrix_eq
  exact product_44_left.trans product_44_right.symm

private def product_45_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(1, e5), (5, e1)],
    [(0, e3), (6, e1)],
    [(2, e5), (7, e1)],
    [(8, e1)],
    [(3, e5), (9, e1)],
    [(10, e1)],
    [(4, e5), (11, e1)],
    [(12, e1)],
    [(0, e2), (6, e5), (13, e1)],
    [(1, e6), (5, e3), (14, e1)],
    [(15, e1)],
    [(2, e6), (7, e3), (16, e1)],
    [(17, e1)],
    [(3, e6), (9, e3), (18, e1)],
    [(0, e4), (6, e7), (12, e5), (19, e1)],
    [(4, e6), (11, e3), (20, e1)],
    [(1, e5), (5, e2), (14, e5), (21, e1)],
    [(2, e5), (7, e2), (16, e5), (22, e1)],
    [(3, e5), (9, e2), (18, e5), (23, e1)],
    [(4, e5), (11, e2), (20, e5), (24, e1)],
    [(0, e3), (6, e6), (12, e6), (19, e3), (25, e1)]])
private theorem product_45_left_s1 : wordMatrix [Atom.root 6 4] = atomMatrix (Atom.root 6 4) := by simp
private theorem product_45_left_s0 : wordMatrix [Atom.root 6 1, Atom.root 6 4] = product_45_target := by
  rw [wordMatrix_cons, product_45_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 6 1))
  decide +kernel
private theorem product_45_left : wordMatrix [Atom.root 6 1, Atom.root 6 4] = product_45_target := product_45_left_s0
private theorem product_45_right_s1 : wordMatrix [Atom.root 11 2] = atomMatrix (Atom.root 11 2) := by simp
private theorem product_45_right_s0 : wordMatrix [Atom.root 6 5, Atom.root 11 2] = product_45_target := by
  rw [wordMatrix_cons, product_45_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 6 5))
  decide +kernel
private theorem product_45_right : wordMatrix [Atom.root 6 5, Atom.root 11 2] = product_45_target := product_45_right_s0
theorem product_45 : wordGroup (product_lhs 45) = wordGroup (product_rhs 45) := by
  apply word_eq_of_matrix_eq
  exact product_45_left.trans product_45_right.symm

private def product_46_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(1, e4), (5, e1)],
    [(0, e2), (6, e1)],
    [(2, e4), (7, e1)],
    [(8, e1)],
    [(3, e4), (9, e1)],
    [(10, e1)],
    [(4, e4), (11, e1)],
    [(12, e1)],
    [(0, e3), (6, e4), (13, e1)],
    [(5, e2), (14, e1)],
    [(15, e1)],
    [(7, e2), (16, e1)],
    [(17, e1)],
    [(9, e2), (18, e1)],
    [(6, e6), (12, e4), (19, e1)],
    [(11, e2), (20, e1)],
    [(1, e7), (5, e3), (14, e4), (21, e1)],
    [(2, e7), (7, e3), (16, e4), (22, e1)],
    [(3, e7), (9, e3), (18, e4), (23, e1)],
    [(4, e7), (11, e3), (20, e4), (24, e1)],
    [(0, e5), (6, e7), (19, e2), (25, e1)]])
private theorem product_46_left_s1 : wordMatrix [Atom.root 6 5] = atomMatrix (Atom.root 6 5) := by simp
private theorem product_46_left_s0 : wordMatrix [Atom.root 6 1, Atom.root 6 5] = product_46_target := by
  rw [wordMatrix_cons, product_46_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 6 1))
  decide +kernel
private theorem product_46_left : wordMatrix [Atom.root 6 1, Atom.root 6 5] = product_46_target := product_46_left_s0
private theorem product_46_right_s1 : wordMatrix [Atom.root 11 3] = atomMatrix (Atom.root 11 3) := by simp
private theorem product_46_right_s0 : wordMatrix [Atom.root 6 4, Atom.root 11 3] = product_46_target := by
  rw [wordMatrix_cons, product_46_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 6 4))
  decide +kernel
private theorem product_46_right : wordMatrix [Atom.root 6 4, Atom.root 11 3] = product_46_target := product_46_right_s0
theorem product_46 : wordGroup (product_lhs 46) = wordGroup (product_rhs 46) := by
  apply word_eq_of_matrix_eq
  exact product_46_left.trans product_46_right.symm

private def product_47_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(1, e7), (5, e1)],
    [(0, e5), (6, e1)],
    [(2, e7), (7, e1)],
    [(8, e1)],
    [(3, e7), (9, e1)],
    [(10, e1)],
    [(4, e7), (11, e1)],
    [(12, e1)],
    [(0, e4), (6, e7), (13, e1)],
    [(1, e2), (5, e5), (14, e1)],
    [(15, e1)],
    [(2, e2), (7, e5), (16, e1)],
    [(17, e1)],
    [(3, e2), (9, e5), (18, e1)],
    [(0, e6), (6, e3), (12, e7), (19, e1)],
    [(4, e2), (11, e5), (20, e1)],
    [(1, e7), (5, e4), (14, e7), (21, e1)],
    [(2, e7), (7, e4), (16, e7), (22, e1)],
    [(3, e7), (9, e4), (18, e7), (23, e1)],
    [(4, e7), (11, e4), (20, e7), (24, e1)],
    [(0, e5), (6, e2), (12, e2), (19, e5), (25, e1)]])
private theorem product_47_left_s1 : wordMatrix [Atom.root 6 6] = atomMatrix (Atom.root 6 6) := by simp
private theorem product_47_left_s0 : wordMatrix [Atom.root 6 1, Atom.root 6 6] = product_47_target := by
  rw [wordMatrix_cons, product_47_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 6 1))
  decide +kernel
private theorem product_47_left : wordMatrix [Atom.root 6 1, Atom.root 6 6] = product_47_target := product_47_left_s0
private theorem product_47_right_s1 : wordMatrix [Atom.root 11 4] = atomMatrix (Atom.root 11 4) := by simp
private theorem product_47_right_s0 : wordMatrix [Atom.root 6 7, Atom.root 11 4] = product_47_target := by
  rw [wordMatrix_cons, product_47_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 6 7))
  decide +kernel
private theorem product_47_right : wordMatrix [Atom.root 6 7, Atom.root 11 4] = product_47_target := product_47_right_s0
theorem product_47 : wordGroup (product_lhs 47) = wordGroup (product_rhs 47) := by
  apply word_eq_of_matrix_eq
  exact product_47_left.trans product_47_right.symm

end Kourovka.Problem2153.WilsonModel.RootData.Relations
