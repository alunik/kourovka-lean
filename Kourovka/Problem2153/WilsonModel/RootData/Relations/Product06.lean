import Kourovka.Problem2153.WilsonModel.RootData.Relations.Metadata
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
namespace Kourovka.Problem2153.WilsonModel.RootData.Relations
open Field8 F8
private def product_36_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(0, e3), (4, e1)],
    [(5, e1)],
    [(1, e3), (6, e1)],
    [(7, e1)],
    [(8, e1)],
    [(1, e7), (9, e1)],
    [(10, e1)],
    [(2, e7), (11, e1)],
    [(5, e3), (12, e1)],
    [(13, e1)],
    [(14, e1)],
    [(7, e3), (15, e1)],
    [(8, e3), (16, e1)],
    [(1, e2), (6, e7), (9, e3), (17, e1)],
    [(10, e3), (18, e1)],
    [(8, e7), (19, e1)],
    [(5, e5), (13, e3), (20, e1)],
    [(21, e1)],
    [(22, e1)],
    [(14, e7), (23, e1)],
    [(8, e2), (16, e7), (19, e3), (24, e1)],
    [(21, e3), (25, e1)]])
private theorem product_36_left_s1 : wordMatrix [Atom.root 5 2] = atomMatrix (Atom.root 5 2) := by simp
private theorem product_36_left_s0 : wordMatrix [Atom.root 5 1, Atom.root 5 2] = product_36_target := by
  rw [wordMatrix_cons, product_36_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 5 1))
  decide +kernel
private theorem product_36_left : wordMatrix [Atom.root 5 1, Atom.root 5 2] = product_36_target := product_36_left_s0
private theorem product_36_right_s0 : wordMatrix [Atom.root 5 3] = atomMatrix (Atom.root 5 3) := by simp
private theorem product_36_right : wordMatrix [Atom.root 5 3] = product_36_target := by
  rw [product_36_right_s0]
  decide +kernel
theorem product_36 : wordGroup (product_lhs 36) = wordGroup (product_rhs 36) := by
  apply word_eq_of_matrix_eq
  exact product_36_left.trans product_36_right.symm

private def product_37_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(0, e2), (4, e1)],
    [(5, e1)],
    [(1, e2), (6, e1)],
    [(7, e1)],
    [(8, e1)],
    [(1, e6), (9, e1)],
    [(10, e1)],
    [(2, e6), (11, e1)],
    [(5, e2), (12, e1)],
    [(13, e1)],
    [(14, e1)],
    [(7, e2), (15, e1)],
    [(8, e2), (16, e1)],
    [(1, e7), (6, e6), (9, e2), (17, e1)],
    [(10, e2), (18, e1)],
    [(8, e6), (19, e1)],
    [(5, e4), (13, e2), (20, e1)],
    [(21, e1)],
    [(22, e1)],
    [(14, e6), (23, e1)],
    [(8, e7), (16, e6), (19, e2), (24, e1)],
    [(21, e2), (25, e1)]])
private theorem product_37_left_s1 : wordMatrix [Atom.root 5 3] = atomMatrix (Atom.root 5 3) := by simp
private theorem product_37_left_s0 : wordMatrix [Atom.root 5 1, Atom.root 5 3] = product_37_target := by
  rw [wordMatrix_cons, product_37_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 5 1))
  decide +kernel
private theorem product_37_left : wordMatrix [Atom.root 5 1, Atom.root 5 3] = product_37_target := product_37_left_s0
private theorem product_37_right_s0 : wordMatrix [Atom.root 5 2] = atomMatrix (Atom.root 5 2) := by simp
private theorem product_37_right : wordMatrix [Atom.root 5 2] = product_37_target := by
  rw [product_37_right_s0]
  decide +kernel
theorem product_37 : wordGroup (product_lhs 37) = wordGroup (product_rhs 37) := by
  apply word_eq_of_matrix_eq
  exact product_37_left.trans product_37_right.symm

private def product_38_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(0, e5), (4, e1)],
    [(5, e1)],
    [(1, e5), (6, e1)],
    [(7, e1)],
    [(8, e1)],
    [(1, e3), (9, e1)],
    [(10, e1)],
    [(2, e3), (11, e1)],
    [(5, e5), (12, e1)],
    [(13, e1)],
    [(14, e1)],
    [(7, e5), (15, e1)],
    [(8, e5), (16, e1)],
    [(1, e4), (6, e3), (9, e5), (17, e1)],
    [(10, e5), (18, e1)],
    [(8, e3), (19, e1)],
    [(5, e7), (13, e5), (20, e1)],
    [(21, e1)],
    [(22, e1)],
    [(14, e3), (23, e1)],
    [(8, e4), (16, e3), (19, e5), (24, e1)],
    [(21, e5), (25, e1)]])
private theorem product_38_left_s1 : wordMatrix [Atom.root 5 4] = atomMatrix (Atom.root 5 4) := by simp
private theorem product_38_left_s0 : wordMatrix [Atom.root 5 1, Atom.root 5 4] = product_38_target := by
  rw [wordMatrix_cons, product_38_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 5 1))
  decide +kernel
private theorem product_38_left : wordMatrix [Atom.root 5 1, Atom.root 5 4] = product_38_target := product_38_left_s0
private theorem product_38_right_s0 : wordMatrix [Atom.root 5 5] = atomMatrix (Atom.root 5 5) := by simp
private theorem product_38_right : wordMatrix [Atom.root 5 5] = product_38_target := by
  rw [product_38_right_s0]
  decide +kernel
theorem product_38 : wordGroup (product_lhs 38) = wordGroup (product_rhs 38) := by
  apply word_eq_of_matrix_eq
  exact product_38_left.trans product_38_right.symm

private def product_39_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(0, e4), (4, e1)],
    [(5, e1)],
    [(1, e4), (6, e1)],
    [(7, e1)],
    [(8, e1)],
    [(1, e2), (9, e1)],
    [(10, e1)],
    [(2, e2), (11, e1)],
    [(5, e4), (12, e1)],
    [(13, e1)],
    [(14, e1)],
    [(7, e4), (15, e1)],
    [(8, e4), (16, e1)],
    [(1, e3), (6, e2), (9, e4), (17, e1)],
    [(10, e4), (18, e1)],
    [(8, e2), (19, e1)],
    [(5, e6), (13, e4), (20, e1)],
    [(21, e1)],
    [(22, e1)],
    [(14, e2), (23, e1)],
    [(8, e3), (16, e2), (19, e4), (24, e1)],
    [(21, e4), (25, e1)]])
private theorem product_39_left_s1 : wordMatrix [Atom.root 5 5] = atomMatrix (Atom.root 5 5) := by simp
private theorem product_39_left_s0 : wordMatrix [Atom.root 5 1, Atom.root 5 5] = product_39_target := by
  rw [wordMatrix_cons, product_39_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 5 1))
  decide +kernel
private theorem product_39_left : wordMatrix [Atom.root 5 1, Atom.root 5 5] = product_39_target := product_39_left_s0
private theorem product_39_right_s0 : wordMatrix [Atom.root 5 4] = atomMatrix (Atom.root 5 4) := by simp
private theorem product_39_right : wordMatrix [Atom.root 5 4] = product_39_target := by
  rw [product_39_right_s0]
  decide +kernel
theorem product_39 : wordGroup (product_lhs 39) = wordGroup (product_rhs 39) := by
  apply word_eq_of_matrix_eq
  exact product_39_left.trans product_39_right.symm

private def product_40_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(0, e7), (4, e1)],
    [(5, e1)],
    [(1, e7), (6, e1)],
    [(7, e1)],
    [(8, e1)],
    [(1, e5), (9, e1)],
    [(10, e1)],
    [(2, e5), (11, e1)],
    [(5, e7), (12, e1)],
    [(13, e1)],
    [(14, e1)],
    [(7, e7), (15, e1)],
    [(8, e7), (16, e1)],
    [(1, e6), (6, e5), (9, e7), (17, e1)],
    [(10, e7), (18, e1)],
    [(8, e5), (19, e1)],
    [(5, e3), (13, e7), (20, e1)],
    [(21, e1)],
    [(22, e1)],
    [(14, e5), (23, e1)],
    [(8, e6), (16, e5), (19, e7), (24, e1)],
    [(21, e7), (25, e1)]])
private theorem product_40_left_s1 : wordMatrix [Atom.root 5 6] = atomMatrix (Atom.root 5 6) := by simp
private theorem product_40_left_s0 : wordMatrix [Atom.root 5 1, Atom.root 5 6] = product_40_target := by
  rw [wordMatrix_cons, product_40_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 5 1))
  decide +kernel
private theorem product_40_left : wordMatrix [Atom.root 5 1, Atom.root 5 6] = product_40_target := product_40_left_s0
private theorem product_40_right_s0 : wordMatrix [Atom.root 5 7] = atomMatrix (Atom.root 5 7) := by simp
private theorem product_40_right : wordMatrix [Atom.root 5 7] = product_40_target := by
  rw [product_40_right_s0]
  decide +kernel
theorem product_40 : wordGroup (product_lhs 40) = wordGroup (product_rhs 40) := by
  apply word_eq_of_matrix_eq
  exact product_40_left.trans product_40_right.symm

private def product_41_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(0, e6), (4, e1)],
    [(5, e1)],
    [(1, e6), (6, e1)],
    [(7, e1)],
    [(8, e1)],
    [(1, e4), (9, e1)],
    [(10, e1)],
    [(2, e4), (11, e1)],
    [(5, e6), (12, e1)],
    [(13, e1)],
    [(14, e1)],
    [(7, e6), (15, e1)],
    [(8, e6), (16, e1)],
    [(1, e5), (6, e4), (9, e6), (17, e1)],
    [(10, e6), (18, e1)],
    [(8, e4), (19, e1)],
    [(5, e2), (13, e6), (20, e1)],
    [(21, e1)],
    [(22, e1)],
    [(14, e4), (23, e1)],
    [(8, e5), (16, e4), (19, e6), (24, e1)],
    [(21, e6), (25, e1)]])
private theorem product_41_left_s1 : wordMatrix [Atom.root 5 7] = atomMatrix (Atom.root 5 7) := by simp
private theorem product_41_left_s0 : wordMatrix [Atom.root 5 1, Atom.root 5 7] = product_41_target := by
  rw [wordMatrix_cons, product_41_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 5 1))
  decide +kernel
private theorem product_41_left : wordMatrix [Atom.root 5 1, Atom.root 5 7] = product_41_target := product_41_left_s0
private theorem product_41_right_s0 : wordMatrix [Atom.root 5 6] = atomMatrix (Atom.root 5 6) := by simp
private theorem product_41_right : wordMatrix [Atom.root 5 6] = product_41_target := by
  rw [product_41_right_s0]
  decide +kernel
theorem product_41 : wordGroup (product_lhs 41) = wordGroup (product_rhs 41) := by
  apply word_eq_of_matrix_eq
  exact product_41_left.trans product_41_right.symm

end Kourovka.Problem2153.WilsonModel.RootData.Relations
