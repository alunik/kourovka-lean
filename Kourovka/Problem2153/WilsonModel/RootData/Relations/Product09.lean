import Kourovka.Problem2153.WilsonModel.RootData.Relations.Metadata
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
namespace Kourovka.Problem2153.WilsonModel.RootData.Relations
open Field8 F8
private def product_54_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(0, e7), (5, e1)],
    [(6, e1)],
    [(7, e1)],
    [(0, e5), (2, e7), (8, e1)],
    [(9, e1)],
    [(3, e7), (10, e1)],
    [(11, e1)],
    [(4, e7), (12, e1)],
    [(4, e7), (13, e1)],
    [(3, e5), (6, e7), (14, e1)],
    [(15, e1)],
    [(4, e5), (16, e1)],
    [(17, e1)],
    [(18, e1)],
    [(11, e7), (19, e1)],
    [(20, e1)],
    [(4, e3), (9, e5), (12, e7), (13, e7), (21, e1)],
    [(11, e5), (15, e7), (22, e1)],
    [(17, e7), (23, e1)],
    [(24, e1)],
    [(17, e5), (20, e7), (25, e1)]])
private theorem product_54_left_s1 : wordMatrix [Atom.root 7 6] = atomMatrix (Atom.root 7 6) := by simp
private theorem product_54_left_s0 : wordMatrix [Atom.root 7 1, Atom.root 7 6] = product_54_target := by
  rw [wordMatrix_cons, product_54_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 7 1))
  decide +kernel
private theorem product_54_left : wordMatrix [Atom.root 7 1, Atom.root 7 6] = product_54_target := product_54_left_s0
private theorem product_54_right_s0 : wordMatrix [Atom.root 7 7] = atomMatrix (Atom.root 7 7) := by simp
private theorem product_54_right : wordMatrix [Atom.root 7 7] = product_54_target := by
  rw [product_54_right_s0]
  decide +kernel
theorem product_54 : wordGroup (product_lhs 54) = wordGroup (product_rhs 54) := by
  apply word_eq_of_matrix_eq
  exact product_54_left.trans product_54_right.symm

private def product_55_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(0, e6), (5, e1)],
    [(6, e1)],
    [(7, e1)],
    [(0, e4), (2, e6), (8, e1)],
    [(9, e1)],
    [(3, e6), (10, e1)],
    [(11, e1)],
    [(4, e6), (12, e1)],
    [(4, e6), (13, e1)],
    [(3, e4), (6, e6), (14, e1)],
    [(15, e1)],
    [(4, e4), (16, e1)],
    [(17, e1)],
    [(18, e1)],
    [(11, e6), (19, e1)],
    [(20, e1)],
    [(4, e2), (9, e4), (12, e6), (13, e6), (21, e1)],
    [(11, e4), (15, e6), (22, e1)],
    [(17, e6), (23, e1)],
    [(24, e1)],
    [(17, e4), (20, e6), (25, e1)]])
private theorem product_55_left_s1 : wordMatrix [Atom.root 7 7] = atomMatrix (Atom.root 7 7) := by simp
private theorem product_55_left_s0 : wordMatrix [Atom.root 7 1, Atom.root 7 7] = product_55_target := by
  rw [wordMatrix_cons, product_55_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 7 1))
  decide +kernel
private theorem product_55_left : wordMatrix [Atom.root 7 1, Atom.root 7 7] = product_55_target := product_55_left_s0
private theorem product_55_right_s0 : wordMatrix [Atom.root 7 6] = atomMatrix (Atom.root 7 6) := by simp
private theorem product_55_right : wordMatrix [Atom.root 7 6] = product_55_target := by
  rw [product_55_right_s0]
  decide +kernel
theorem product_55 : wordGroup (product_lhs 55) = wordGroup (product_rhs 55) := by
  apply word_eq_of_matrix_eq
  exact product_55_left.trans product_55_right.symm

private def product_56_target : Mat := 1
private theorem product_56_left_s1 : wordMatrix [Atom.root 8 1] = atomMatrix (Atom.root 8 1) := by simp
private theorem product_56_left_s0 : wordMatrix [Atom.root 8 1, Atom.root 8 1] = product_56_target := by
  rw [wordMatrix_cons, product_56_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 8 1))
  decide +kernel
private theorem product_56_left : wordMatrix [Atom.root 8 1, Atom.root 8 1] = product_56_target := product_56_left_s0
private theorem product_56_right : wordMatrix [] = product_56_target := by decide +kernel
theorem product_56 : wordGroup (product_lhs 56) = wordGroup (product_rhs 56) := by
  apply word_eq_of_matrix_eq
  exact product_56_left.trans product_56_right.symm

private def product_57_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(5, e1)],
    [(6, e1)],
    [(0, e3), (7, e1)],
    [(1, e3), (8, e1)],
    [(9, e1)],
    [(0, e7), (10, e1)],
    [(11, e1)],
    [(3, e3), (12, e1)],
    [(13, e1)],
    [(2, e7), (14, e1)],
    [(4, e3), (15, e1)],
    [(6, e3), (16, e1)],
    [(17, e1)],
    [(4, e7), (18, e1)],
    [(9, e3), (19, e1)],
    [(20, e1)],
    [(0, e2), (7, e7), (10, e3), (21, e1)],
    [(3, e5), (13, e3), (22, e1)],
    [(11, e7), (23, e1)],
    [(17, e3), (24, e1)],
    [(4, e2), (15, e7), (18, e3), (25, e1)]])
private theorem product_57_left_s1 : wordMatrix [Atom.root 8 2] = atomMatrix (Atom.root 8 2) := by simp
private theorem product_57_left_s0 : wordMatrix [Atom.root 8 1, Atom.root 8 2] = product_57_target := by
  rw [wordMatrix_cons, product_57_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 8 1))
  decide +kernel
private theorem product_57_left : wordMatrix [Atom.root 8 1, Atom.root 8 2] = product_57_target := product_57_left_s0
private theorem product_57_right_s0 : wordMatrix [Atom.root 8 3] = atomMatrix (Atom.root 8 3) := by simp
private theorem product_57_right : wordMatrix [Atom.root 8 3] = product_57_target := by
  rw [product_57_right_s0]
  decide +kernel
theorem product_57 : wordGroup (product_lhs 57) = wordGroup (product_rhs 57) := by
  apply word_eq_of_matrix_eq
  exact product_57_left.trans product_57_right.symm

private def product_58_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(5, e1)],
    [(6, e1)],
    [(0, e2), (7, e1)],
    [(1, e2), (8, e1)],
    [(9, e1)],
    [(0, e6), (10, e1)],
    [(11, e1)],
    [(3, e2), (12, e1)],
    [(13, e1)],
    [(2, e6), (14, e1)],
    [(4, e2), (15, e1)],
    [(6, e2), (16, e1)],
    [(17, e1)],
    [(4, e6), (18, e1)],
    [(9, e2), (19, e1)],
    [(20, e1)],
    [(0, e7), (7, e6), (10, e2), (21, e1)],
    [(3, e4), (13, e2), (22, e1)],
    [(11, e6), (23, e1)],
    [(17, e2), (24, e1)],
    [(4, e7), (15, e6), (18, e2), (25, e1)]])
private theorem product_58_left_s1 : wordMatrix [Atom.root 8 3] = atomMatrix (Atom.root 8 3) := by simp
private theorem product_58_left_s0 : wordMatrix [Atom.root 8 1, Atom.root 8 3] = product_58_target := by
  rw [wordMatrix_cons, product_58_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 8 1))
  decide +kernel
private theorem product_58_left : wordMatrix [Atom.root 8 1, Atom.root 8 3] = product_58_target := product_58_left_s0
private theorem product_58_right_s0 : wordMatrix [Atom.root 8 2] = atomMatrix (Atom.root 8 2) := by simp
private theorem product_58_right : wordMatrix [Atom.root 8 2] = product_58_target := by
  rw [product_58_right_s0]
  decide +kernel
theorem product_58 : wordGroup (product_lhs 58) = wordGroup (product_rhs 58) := by
  apply word_eq_of_matrix_eq
  exact product_58_left.trans product_58_right.symm

private def product_59_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(5, e1)],
    [(6, e1)],
    [(0, e5), (7, e1)],
    [(1, e5), (8, e1)],
    [(9, e1)],
    [(0, e3), (10, e1)],
    [(11, e1)],
    [(3, e5), (12, e1)],
    [(13, e1)],
    [(2, e3), (14, e1)],
    [(4, e5), (15, e1)],
    [(6, e5), (16, e1)],
    [(17, e1)],
    [(4, e3), (18, e1)],
    [(9, e5), (19, e1)],
    [(20, e1)],
    [(0, e4), (7, e3), (10, e5), (21, e1)],
    [(3, e7), (13, e5), (22, e1)],
    [(11, e3), (23, e1)],
    [(17, e5), (24, e1)],
    [(4, e4), (15, e3), (18, e5), (25, e1)]])
private theorem product_59_left_s1 : wordMatrix [Atom.root 8 4] = atomMatrix (Atom.root 8 4) := by simp
private theorem product_59_left_s0 : wordMatrix [Atom.root 8 1, Atom.root 8 4] = product_59_target := by
  rw [wordMatrix_cons, product_59_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 8 1))
  decide +kernel
private theorem product_59_left : wordMatrix [Atom.root 8 1, Atom.root 8 4] = product_59_target := product_59_left_s0
private theorem product_59_right_s0 : wordMatrix [Atom.root 8 5] = atomMatrix (Atom.root 8 5) := by simp
private theorem product_59_right : wordMatrix [Atom.root 8 5] = product_59_target := by
  rw [product_59_right_s0]
  decide +kernel
theorem product_59 : wordGroup (product_lhs 59) = wordGroup (product_rhs 59) := by
  apply word_eq_of_matrix_eq
  exact product_59_left.trans product_59_right.symm

end Kourovka.Problem2153.WilsonModel.RootData.Relations
